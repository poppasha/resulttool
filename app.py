"""
MSBTE Tool - Web App (NiceGUI)
==============================
Left sidebar with all 5 modes (locked until the previous one is
complete), right panel with a shared enrollment-numbers area up top
and a mode-specific content area below it.

Train mode is fully wired up to msbte_tool.py's existing (non-tkinter)
logic: fetch_result_html's HTTP/form-parsing steps, expand_table_grid,
extract_semester_label, group_tables, cross_check_samples,
apply_mapping_to_chunk, save_semester_headings_to_db. Only the
tkinter-specific *dialog*/*popup* functions in msbte_tool.py are
replaced -- with an in-browser captcha dialog and a click-based
rectangle selector instead of the drag-based tkinter SelectableGrid.

Run with:
    python app.py
Then open the URL it prints (defaults to http://localhost:8080).
"""

import asyncio
import base64
import datetime
import html as html_lib
import json
import os
import random
import shutil
import sqlite3
import string

import requests
from bs4 import BeautifulSoup

from nicegui import ui, run

import msbte_tool as mt

MODES = [
    ("seating", "Seating Chart", "event_seat"),
    ("train", "Train", "school"),
    ("extract", "Extract", "download"),
    ("coursecodes", "Course Codes", "menu_book"),
    ("offline", "Offline Import", "cloud_off"),
    ("recheck", "Recheck", "fact_check"),
    ("report", "Report", "picture_as_pdf"),
]

MODE_DESCRIPTIONS = {
    "train": (
        "One-time setup per semester. Enter a few sample enrollment numbers above, "
        "fetch each live (solve the captcha when it appears), then mark which cells "
        "belong to each field per semester. This teaches the tool the page layout -- "
        "nothing about row/column position is hardcoded."
    ),
    "extract": (
        "Everyday use. Paste enrollment numbers above (one per line), then fetch. "
        "Each one needs its captcha solved once. Results are saved straight to the "
        "database -- one failure doesn't stop the batch."
    ),
    "recheck": (
        "For students whose marks changed after a rechecking application. Choose "
        "Automatic (re-fetch live, same captcha flow, using the enrollments pasted "
        "above) or Manual (type in corrected marks yourself, semester by semester)."
    ),
    "report": (
        "Build PDF reports straight from the database -- no fetching, no captchas. "
        "Choose which report(s) to build and whether to include Regular, EX, or both."
    ),
    "coursecodes": (
        "One-time manual data entry: fill in Abbreviation / Course Code / Faculty for "
        "every subject, per semester. Supports pasting a block of cells from Excel."
    ),
    "offline": (
        "Fallback for when MSBTE's site or data is unavailable. Builds the exact same "
        "database Train + Extract mode would have -- you declare each subject's "
        "structure once (like Train mode), then paste every student's marks in bulk "
        "(like Extract mode), all typed/pasted instead of fetched live."
    ),
    "seating": (
        "Import MSBTE's own seating chart to give every report a ground-truth answer "
        "for Regular vs EX, per student per semester -- instead of guessing from "
        "which semesters a student happens to have marks data for."
    ),
}

# Sequence Train -> Extract -> Course Codes -> Offline Import -> Recheck
# is communicated (via mark_complete_and_advance), not enforced -- and
# no longer scheme-scoped. Seating Chart is the only mode that still
# deals with scheme letters (it's what discovers them); Report works
# across the whole database with its own independent scheme picker.
MODE_ORDER = ["train", "extract", "coursecodes", "offline", "recheck"]

# The identity fields (Program/Name/Enrollment/.../Semester) and summary
# fields (Total Marks/.../Result) are simple, always-one-shape fields --
# unaffected by which scheme's subject-table grammar is in play -- so
# they keep using the original flat range-selector below. Only the
# subject-table part (subjects/maximum_marks/obtained_marks/thprsla/fasa)
# is replaced by the new Subject-wise Step 1/2 trainer further down,
# since THAT part is what actually differs between K-scheme, I-scheme,
# and whatever MSBTE does next.
SUBJECT_TABLE_GROUP_KEYS = {"subjects", "maximum_marks", "obtained_marks", "thprsla", "fasa"}
NON_SUBJECT_GROUPS = [g for g in mt.GROUPS if g[0] not in SUBJECT_TABLE_GROUP_KEYS]

REPORTS_DIR = "reports"
GAP_UPLOAD_DIR = "gap_uploads"

REPORT_LABELS = {
    "semester": "Semester-wise Report(s)",
    "yearly_result": "Yearly Result Report",
    "k7_partb": "K7 (Part B) Report",
    "k7_partc": "K7 (Part C) Report",
    "yearly_eligibility": "Yearly Eligible/Non-Eligible Student List",
    "topper_list": "Semesterwise and Yearly Topper List",
    "bright_weak": "Semester wise Bright/Weak Student List",
    "departmental": "Departmental Report",
}
REPORT_ORDER = list(REPORT_LABELS.keys())

REPORT_STATUS_OPTIONS = {
    "regular": "Regular students only",
    "ex": "EX students only",
    "both": "Both Regular and EX",
}

# ---------------------------------------------------------------------
# Shared app state
# ---------------------------------------------------------------------
state = {
    "mode": "train",
    "enrollment_text": "",
    "train_enrollments_text": "",  # newline-separated sample enrollment numbers, any count -- pastes
                                    # directly from Seating Chart's "Recommended Enrollment Numbers
                                    # for Train Mode" list
    # Flat completion tracking -- ticking a mode complete is purely
    # informational bookkeeping (nothing is gated on it). Scheme no
    # longer scopes this: Train/Extract/Course Codes/Recheck/Offline
    # each work over whatever data the user pasted in, full stop.
    "completed": set(),

    # Train-mode flow: "input" -> "fetching" -> "select_ranges" -> "done"
    "train_step": "input",
    "train_fetch_log": [],
    "captcha_pending": None,  # {"b64", "done" (asyncio.Event), "result"} while awaiting input -- shared by any mode that fetches live (train, extract, recheck-automatic)
    # Fetch-loop control (Train's "fetching" step): "current_task" is the
    # asyncio Task for whichever ONE enrollment is being fetched right
    # now -- cancelling just it (Skip This Enrollment) moves on to the
    # next enrollment without aborting the whole batch. "stop_requested"
    # additionally breaks the loop itself (Stop / Back to Input) rather
    # than continuing to the next enrollment after the current one is
    # abandoned.
    "train_fetch_current_task": None,
    "train_fetch_stop_requested": False,
    "train_samples": {},        # semester_label -> [(enrollment, chunk), ...]
    "train_warnings": [],
    "train_order": [],          # semester labels, in the order to process them
    "train_current_idx": 0,
    "train_mapping": {},        # label -> {group_key: {"ranges": [...]}}, built as we go
    "train_collected": {key: [] for key, _ in mt.GROUPS},
    "train_import_checked": True,  # "import same addresses as previous semester" checkbox, per semester
    "train_pending_rects": {},  # position -> [(r0, r1, c0, c1), ...] committed-in-grid, not yet added
    "train_anchor": {},         # position -> (r, c), set on mousedown until the matching mouseup
    "train_last_active_position": None,
    "train_institute_name": "",
    "train_institute_address": "",

    # Subject-wise trainer v3 -- ONE drag per concept, in this exact
    # order: Whole Table -> Subjects -> Level 1 -> Level 2 -> ... ->
    # Max+Obtained. No per-subject or per-leaf clicking; the component
    # tree, per-subject enable/disable, and Max/Obtained cell positions
    # are all derived automatically from these few drags -- see
    # mt.finalize_subjectwise_training_horizontal/_vertical().
    "train_cell_text": {},           # (position, r, c) -> cell's actual text, filled by render_grid
    "train_wizard_anchor": None,     # (position, r, c) mousedown target for the CURRENT drag
    "train_wizard_pending": None,    # {"position","row_start","row_end","col_start","col_end"} drawn,
                                      # awaiting Confirm -- exactly one at a time, by design
    "train_whole_table_drag": None,
    "train_subjects_drag": None,
    "train_subjects_preview": [],    # [{"subject_index","subject_name","row_start","row_end"}, ...]
    "train_orientation": None,       # "horizontal" | "vertical" | None
    "train_level_count": None,       # chosen via dropdown in the subject-wise panel's sidebar
    "train_level_drags": [None] * mt.MAX_TEMPLATE_LEVELS,  # fixed-size, index i = Level i+1's rect
    "train_level_card_containers": {},  # {level_index: card element} -- pre-built, shown/hidden
    "train_level_hint_labels": {},       # {level_index: label element} -- text updated on orientation change
    "train_subjects_count_label": None,  # label element showing "N subject(s) found"
    "train_values_drag": None,
    "train_last_trained_subjects": [],
    "train_last_trained_nodes": [],
    "train_preview_records": [],     # [{subject_index, node_id, role, value}, ...] from re-reading the
                                      # sample page through the just-trained extractor -- shown as a
                                      # tree on the "trained!" screen so wrong cells show up immediately
    "train_preview_review": [],      # [{"enrollment","semester_label","reason"}, ...] from that same
                                      # re-read -- rows/subjects the trained template couldn't match
    "train_preview_enr": None,

    # Live element refs for the current semester's range-selector, so
    # clicks/Add/Clear can update just the affected cell/icon directly
    # instead of rebuilding (and scroll-jumping) the whole panel.
    "train_cell_elements": {},  # (position, r, c) -> td element
    "train_group_icons": {},    # group_key -> icon element

    # Extract-mode flow: "idle" -> "running" -> "done"
    "extract_step": "idle",
    "extract_log": [],
    "extract_summary": None,  # {"processed", "skipped", "extracted", "canonical", "subjectwise", "review"} once done
    "extract_review_details": [],  # [{"enrollment","semester_label","reason"}, ...] from the run just done
    # Progress monitor: extracted (incl. ones already in the database when the run
    # started) vs still-to-extract, out of the pasted total.
    "extract_total": 0,
    "extract_done_list": [],
    "extract_pending_list": [],
    "extract_stop_requested": False,
    "extract_run_id": 0,   # bumped to abort an in-flight run (e.g. on scheme switch)

    # Course Codes mode: loaded once per entry (or on manual reload),
    # edited in place, saved on demand.
    "coursecode_data": None,          # [(sem, [(subject_index, subject_name, [(node_id, label), ...]), ...]), ...]
    "coursecode_values": {},          # (sem, subject_index) -> {"abbreviation", "course_code"}
    "coursecode_faculty_values": {},  # (sem, subject_index, node_id) -> faculty_name
    "coursecode_faculty_touched": set(),  # {(sem, subject_index, node_id), ...} edited individually --
    "coursecode_autofill": False,     # checkbox state: random-fill empty boxes
    "coursecode_autofilled_keys": set(),  # keys whose value was set by autofill (not the user)
    #   for abbreviation/course_code: (sem, subject_index, "abbreviation"/"course_code")
    #   for faculty: (sem, subject_index, node_id)
                                       # exempt from same-subject auto-propagate

    # Report mode: "select" -> "generating" -> "done"
    "report_step": "select",
    "report_log": [],
    "report_generated_files": [],  # [(label, path), ...] once done
    "report_categories": [],       # categories found for the active scheme (refreshed on entering Report)

    # Report mode UI: which report rows are expanded, in the order they
    # were opened (append-only) -- drives the right-hand panel stacking.
    # "yearly_result" stands in for the combined Yearly Result +
    # Yearly Eligible/Non-Eligible row.
    "report_panel_open": [],
    "report_panel_container": None,  # right-panel element, rebuilt on toggle

    # Yearly Report Gap Check: run on demand only (Check button), never
    # automatically -- see run_yearly_gap_check(). Mirrors whatever's
    # currently on record in the yearly_gap_flags DB table.
    # Yearly Result Report / Yearly Eligible-Non-Eligible List: which of
    # the two report modes is currently selected in the combined panel.
    # "gap_check" (default, Option 2) is today's existing behavior --
    # Gap Check required, secondary-db upload available, full yearly
    # aggregate + Eligibility List. "simple" (Option 1) skips the Gap
    # Check/upload entirely and generates immediately from whatever
    # semesters already exist, WITHOUT the yearly aggregate columns --
    # Yearly Eligibility List is unavailable in this mode (its entire
    # output IS that aggregate, so there's nothing for it to produce).
    "yearly_report_mode": "gap_check",

    "yearly_gaps": [],  # [{"enrollment", "year_label", "present_semester", "missing_semester"}, ...]

    # Secondary-database upload for filling gaps: two explicit steps --
    # (1) upload -> READ-ONLY match check (see check_yearly_gap_matches()),
    # shown with a found/not-found mark per gap, nothing written yet;
    # (2) "Update Database" button -> actually copies the matched rows in
    # (see fill_yearly_gaps_from_secondary_db()).
    "yearly_gap_upload_path": None,  # path of the last uploaded secondary db, or None
    "yearly_gap_upload_name": None,  # its original filename, for display
    "yearly_gap_matches": [],        # [{..gap fields.., "found": bool}, ...] from the last check

    # K7 (Part C) Level 1 / FA / SA label choice: one GLOBAL mapping
    # (scheme-agnostic -- applied to every semester, not per-semester).
    # "reference_semester" only controls which semester's own trained
    # hierarchy populates the dropdown option lists; the three chosen
    # label strings themselves are what actually get saved and applied.
    "k7c_reference_semester": None,       # semester_label whose options are shown, or None (defaults to first)
    "k7c_level1_draft": None,
    "k7c_fa_draft": None,
    "k7c_sa_draft": None,

    "report_selection": {
        "semester": {"enabled": True, "statuses": []},
        "yearly_result": {"enabled": False, "statuses": []},
        "k7_partb": {"enabled": True, "statuses": [], "fail_threshold": 30.0},
        "k7_partc": {"enabled": True, "statuses": []},
        "yearly_eligibility": {"enabled": False, "statuses": []},
        "topper_list": {"enabled": True, "statuses": []},
        "bright_weak": {"enabled": True, "statuses": [], "weak_threshold": 40.0, "bright_threshold": 75.0},
        "departmental": {"enabled": False, "statuses": [], "show_pct": False},
    },

    # Departmental Report setup drafts (loaded from the ACTIVE scheme's database; dept_loaded_key is
    # that database's path, so switching scheme reloads them).
    "dept_loaded_key": None,
    "dept_classes_draft": [],        # [{"id": int|None, "name": str, "counts_pass": bool}, ...]
    "dept_mapping_draft": {},        # {result text: class_id or None}
    "dept_enrolled_draft": {},       # {(semester_label, category): "text"}
    "dept_program_code_draft": "",
    "dept_sem_off_draft": set(),     # semesters UNticked for the Departmental Report
    "dept_open": {},                 # which setup expansions the user left open {1|2|3: bool}

    # Recheck mode flow: "choose" -> "automatic_running" -> "automatic_done"
    # or "choose" -> "queue_manual_editor" -> "queue_manual_done"
    # or "choose" -> "queue_delete_editor" -> "queue_delete_done"
    "recheck_step": "choose",
    "recheck_log": [],
    "recheck_summary": None,  # {"total", "changed", "unchanged", "failed"} once automatic run finishes

    # Manual/Delete queue: both walk the SAME pasted enrollment list
    # (shared top textarea), snapshotted into recheck_queue_list the
    # moment a run starts.
    "recheck_queue_mode": None,     # "manual" or "delete" while a queue run is active
    "recheck_queue_list": [],       # snapshotted enrollment numbers for this run
    "recheck_queue_pos": 0,         # index into recheck_queue_list currently shown
    "recheck_queue_stats": {},      # running counters, shape depends on mode
    "recheck_queue_log": [],        # [{"enrollment","status","detail"}] for the summary screen

    "recheck_manual_enrollment": "",      # enrollment currently loaded in the queue (manual or delete)
    "recheck_manual_records": None,       # sqlite3.Row list for the loaded enrollment
    "recheck_manual_semesters": [],       # semester labels present for this enrollment, in order
    "recheck_manual_subject_names": {},   # (sem, abs_row) -> subject name
    "recheck_manual_components": {},      # (sem, abs_col) -> THPRSLA component label
    "recheck_manual_values": {},          # (sem, group, abs_row, abs_col) -> current editable value
    "recheck_manual_originals": {},       # same keys -> original DB value, for diffing on save
    "recheck_manual_delete_semesters": set(),  # semester_labels ticked for deletion (Delete queue)
    "recheck_delete_semesters_present": [],    # semesters available to delete for the current Delete queue item

    # Subject/level/leaf marks for semesters trained through the newer
    # tree trainer (subjectwise_student_records), shown alongside the
    # flat student_records marks above for the same enrollment.
    "recheck_manual_subjectwise_values": {},     # (sem, subject_index, node_id, role) -> current editable value
    "recheck_manual_subjectwise_originals": {},  # same keys -> original DB value
    "recheck_manual_subjectwise_meta": {},       # (sem, subject_index, node_id, role) -> {"subject_name","component_label"}

    # Offline Import flow: "setup" (declare semester + subjects, once) ->
    # "paste" (paste + review student rows) -> "done".
    "offline_step": "setup",
    "offline_semester": "",
    "offline_year": "",
    "offline_program": "",
    "offline_subject_count": 1,
    "offline_levels": 2,
    "offline_setup_locked": False,   # False = editing count/name/levels/leaf per subject; True = combined grid
    "offline_subjects": [],   # [{"name","levels","leaf_count","level_labels":[[...]],"max_values":[...]}, ...]
    "offline_template": None,  # result of mt.build_offline_template(), once structure is saved
    "offline_paste_text": "",
    "offline_parsed_rows": None,   # list of list-of-str, after "Parse" is clicked
    "offline_parse_errors": [],
    "offline_saved_count": 0,
    "offline_save_errors": [],

    # Seating Chart: SIX separate global textboxes, one per column
    # heading -- each holds that column's values, one per line, in row
    # order (line 1 of every box together = row 1, etc.). All six are
    # GLOBAL/persistent (not cleared after Save) since they're the
    # standing source of truth, re-combined into rows fresh on every Save.
    "seating_columns": {
        "enrollment": "", "name": "", "seat": "",
        "sem_scheme": "", "regular_ex": "", "subjects": "",
    },
    "seating_parsed_rows": None,
    "seating_parse_errors": [],
    "seating_last_saved_count": None,
    "seating_last_save_errors": [],

    # Which of the two scheme-discovery paths is active -- mutually
    # exclusive by design (see the "real issue" this was built to solve):
    # the user commits to ONE path per session, never both at once.
    # False = paste-based (the original/default path), True = manual entry
    # (for when no seating chart is available at all).
    "seating_manual_mode": False,

    # Paste-path's OWN Year/Session -- deliberately separate state from
    # the manual path's (see seating_manual_year/session below), since
    # only one path is ever active. Program is no longer a typed field
    # at all -- it's always the logged-in department's own name (see
    # state["logged_in"]), read directly wherever Program is needed.
    "seating_paste_year": "",
    "seating_paste_session": "Odd",

    # Manual-path's OWN Year/Session, plus the dynamic "how many
    # schemes" -> that many single-letter textboxes UI.
    "seating_manual_year": "",
    "seating_manual_session": "Odd",
    "seating_manual_scheme_count": "",   # raw text from the "Number of schemes" box
    "seating_manual_scheme_letters": [], # one entry per generated box, index-aligned
    "seating_manual_last_confirmed": None,  # list of scheme letters, after a successful Confirm
    # Import from Institute Seating Chart (department paste screen)
    "seating_import_sitting": None,     # {"year","session"} of the chosen institute database, or None
    "seating_import_program": None,     # Program Code chosen inside it
    "seating_import_semesters": [],     # semester labels chosen for import

    # The Global Scheme Context's current selection -- None until the
    # user picks a radio button in the sidebar. Once set, mt.DB_FILE has
    # already been repointed at this scheme's database (see
    # select_active_scheme() below) -- this dict is purely for DISPLAY
    # (which radio button to show checked, what label to print) and for
    # Phase 3's gating check; nothing about it is passed into Train,
    # Extract, Course Codes, Recheck, Offline Import, or Report.
    "active_scheme": None,  # {"institute", "program", "year", "session", "scheme"} or None

    # Whether the Global Scheme Group's 6 mode buttons are unlocked for
    # the CURRENTLY active scheme -- False the instant a scheme is
    # picked (see select_active_scheme()), and only ever set True by
    # explicitly clicking "Call Global Scheme Group" (fresh) or "Load
    # Prefilled Global Scheme Group" (resume). Switching schemes always
    # resets this back to False, even switching back to a scheme that
    # was already unlocked a moment ago -- re-entry always requires a
    # fresh click.
    "scheme_group_called": False,
    "scheme_picker_container": None,
    "scheme_entry_container": None,
    "operational_modes_container": None,

    # ---------------- AUTHENTICATION ----------------
    # NOTE: like every other key in this module-global `state` dict, this
    # is shared across every browser connection to this server -- fine
    # for single-user/local use (how this app has run throughout), but a
    # real limitation for a genuinely multi-user "live" deployment (one
    # institute's session could observe another's if both connect to the
    # same running server at once). Flagging honestly rather than
    # quietly leaving it as a surprise for later.
    "logged_in": None,      # None, or {"type": "institute", ...}/{"type": "department", ...}
    "auth_view": "login",   # "login" | "signup" | "forgot"
    "login_type": "institute",  # which tab is active on the login screen
    "login_institute_username": "",
    "login_institute_password": "",
    "login_dept_institute_name": "",
    "login_dept_username": "",
    "login_dept_password": "",
    "signup_institute_name": "",
    "signup_username": "",
    "signup_password": "",
    "signup_recovery_email": "",
    "forgot_recovery_email": "",

    # Institute Dashboard, Tile 1 (Generate Departments)
    "gen_dept_count": "",
    "gen_dept_fields": [],  # list of {"name": "", "username": "", "password": ""}, index-aligned

    # Editing an existing department (Tile 1's list) -- None when no row
    # is currently in edit mode; set to that department's id while its
    # inline edit form is open.
    "editing_department_id": None,
    "edit_dept_name": "",
    "edit_dept_username": "",
    "edit_dept_password": "",

    # Institute-level Seating Chart -- completely separate state from
    # Department Seating Chart's (seating_*/seating_manual_* keys above).
    # No shared keys, no shared logic.
    "institute_view": "dashboard",  # "dashboard" | "seating_chart" | "seating_chart_adddel" | "x_table" -- which screen the Institute sees
    "inst_seating_year": "",
    "inst_seating_session": "Odd",
    "inst_seating_columns": {},   # set below, after INSTITUTE_SEATING_COLUMN_SPECS is defined
    "inst_seating_parsed_rows": None,
    "inst_seating_parse_errors": [],
    "inst_seating_last_saved_count": None,
    "inst_seating_last_save_errors": [],
    # Plan 1 additions: preview (parsed-but-not-yet-saved) batch, and the
    # Add/Delete screen's own staging state -- both operate on THIS
    # batch, never on a full reload of everything already in the DB.
    "inst_seating_preview": None,          # list of parsed dicts, or None
    "inst_seating_preview_errors": [],
    "inst_seating_preview_year": "",       # Year/Session captured AT PARSE TIME -- Save/Add/Delete
    "inst_seating_preview_session": "",    # use these, not the live (possibly since-edited) input fields
    "inst_seating_pending_deletes": [],    # list of (enrollment, semester_label, scheme) keys staged for deletion
    "inst_seating_pending_adds": [],       # list of manually-added parsed dicts staged for addition
    "inst_seating_manual_add": {},         # current manual add-row form values, set below
    # Plan 2-5: X Table mode
    "x_table_program": None,   # selected Program Code, or None = show the button list
    "x_table_institute_overview": False,  # Plan 5: viewing the cross-program-code overview screen
    # X Table Level 1 / Level 2 filter -- applied BEFORE anything else in X Table
    "xt_level1_filter": [],
    "xt_level2_filter": [],
    "xt_filter_confirmed": False,
    "xt_filter_key": None,          # (year, session) the confirmed filter belongs to
    # ---------------- Practical Time Table (Tile 2) ----------------
    "ptt_mode": "prerequisites",   # which side-panel mode is active (only one exists so far)
    "ptt_year": "",                # global Institute Seating Chart DB selection, shared by
    "ptt_session": "",             # Button 1 and Button 2 -- selected once in Pre-requisites
    "ptt_db_confirmed": False,     # whether a database has actually been picked yet
    "ptt_active_button": None,     # None | "parent_child"
    # ---------------- Button 1: Parent-Child Subject (Phase C) ----------------
    "pc_program_code": None,       # selected Program Code (single-select)
    "pc_semesters": [],            # selected Semesters (multi-select)
    "pc_selected": {},             # {"sem|scheme|subj|l1|l2": True} -- Section 2 checkbox state
    "pc_child_config": {},         # {"sem|scheme|subj|l1|l2": {"count": int, "children": [str, ...]}}
    "pc_edit_key": None,           # key of the mapping currently being edited in Section 4, or None
    # ---------------- Practical Time Table: exam dates (Phase H) ----------------
    # Semester-wise date ranges editor (the saved groups live in the database)
    "dr_edit_id": None,              # group being edited, or None when adding a new one
    "dr_semesters": [],              # semesters ticked for the range being edited
    "dr_start": "", "dr_end": "",
    "dr_rows": [],                   # [{"date","day","is_exam_day","num_sessions","sessions":[[start,end],...]}]        # (year, session) tuple -- marks which DB's date rows are loaded
    # ---------------- Practical Time Table: batching (Phase I) ----------------
    "batchsetup_loaded_key": None,  # (year, session) tuple
    "batchsetup_rows": {},          # {(pc,sem,scheme): {"num_batches": str, "ranges": [[start,end],...]}}
    "batchsetup_num_input": {},     # {(pc,sem,scheme): str} -- draft "Number of Batches" text, committed on blur/Enter only
    # ---------------- Practical Time Table: subject filter + scheduling matrix (Phase J) ----------------
    "sch4_level1_filter": [],
    "sch4_level2_filter": [],
    "sch4_filter_confirmed": False,
    "sch4_report": None,            # None until "Generate/Refresh Report" clicked; then a static list of row dicts
    "sch4_report_unresolved": [],   # subset of the above rows that couldn't be placed (blank Date/Day/Time + remark)
    "sch4_report_key": None,        # (year, session, level1_filter tuple, level2_filter tuple) the report was generated with
    "wfentry_pending": {},          # {row_id tuple: {"workshop_name": str, "faculty_name": str}} -- Workshop/Faculty Entry section drafts
    "wfentry_locked": {},           # {row_id tuple: bool} -- True = saved & read-only, False = editable
    "wfentry_touched": set(),       # row_ids the user edited by hand (never overwritten by copy/auto-fill)
    "assign_last_unassigned": [],   # last Assign Day & Time run's unassigned batches, with reasons
    "sp_draft": {},                 # semester priority draft: {semester_label: text}
    "subjp_draft": {},              # subject priority draft: {(program,semester,subject): text}
    "fa_selected": set(),           # faculty availability draft: {(faculty, date, session_index)}
    "fa_loaded_key": None,
    "subjp_highlight": "",           # student-count threshold for highlighting a subject row
    "assign_other_last_unassigned": [],
    "wfentry_autofill": False,      # demonstration auto-fill checkbox
    "sch4_report_mode": "auto",     # Practical Time Table Report: "auto" or "manual" date/time allocation
    "sch4_manual_rows": None,       # manual-allocation table rows (built by Generate / Refresh)
    "sch4_manual_slots": {},        # {unit_key: (date, session_index)} manual choices (mirrors the database)
    # ---------------- Online Theory Time Table ----------------
    "ott_year": "", "ott_session": "", "ott_db_confirmed": False,
    "ott_saved": None,               # the saved table of the selected Year/Session (dict) or None
    "ott_saved_key": None,           # (institute, year, session) the above was loaded for
    "ott_edit_mode": False,          # True while editing/regenerating over a saved table
    "ott_programs": [], "ott_semesters": [],     # multi-select: Program Codes and Semesters
    "ott_l1": [], "ott_l2": [], "ott_filter_confirmed": False,
    "ott_selected": set(),           # {(program_code, semester, scheme, subject)} ticked
    "ott_max": {},                   # {(program_code, semester, scheme, subject): "max students per batch" text}
    "ott_times": {},                 # {(program_code, semester, scheme, subject, batch_index): {"date","start","end"}}
    "sch4_saved_loaded_key": None,  # (institute, year, session) whose saved time tables were looked up
    "sch4_saved_meta": {},          # {"auto"/"manual": {generated_at, level1, level2, signature}} of saved tables
    "sch4_manual_auto": set(),      # unit keys in the above that were placed by Auto-fill (not the user)
    "sch4_manual_auto_failures": [],  # last Auto-fill run: ["<batch> -- reason", ...]
    "sch4_manual_key": None,        # filter/db key the manual rows were built for
    "wfentry_auto_values": {},      # {subject_code: {"workshop_name", "faculty_name"}} generated while ticked
    # ---------------- Category Equivalence (Pre-requisites) ----------------
    "ce_loaded_key": None,          # (year, session) the draft below was loaded for
    "ce_selected": set(),           # draft: categories that count as R
}

SEATING_COLUMN_SPECS = [
    ("enrollment", "Enrollment Number"),
    ("name", "Student Name"),
    ("seat", "Seat Number"),
    ("sem_scheme", "Semester-Scheme code (e.g. \"TX-4-K\")"),
    ("regular_ex", "Regular/EX (R = Regular, X = EX, or any other category)"),
    ("subjects", "Subject Appeared (comma-separated)"),
]

# Institute-level Seating Chart's OWN column spec -- deliberately a
# separate constant from SEATING_COLUMN_SPECS above (Department
# Seating Chart's), even though the input shape is identical (same 6
# columns, same paste format) -- no code sharing between the two
# features at all, per the project decision.
INSTITUTE_SEATING_COLUMN_SPECS = [
    ("enrollment", "Enrollment Number"),
    ("name", "Student Name"),
    ("seat", "Seat Number"),
    ("sem_scheme", "Semester-Scheme code (e.g. \"TX-4-K\")"),
    ("regular_ex", "Regular/EX (R = Regular, X = EX, or any other category)"),
    ("subjects", "Subject Appeared (comma-separated)"),
]
state["inst_seating_columns"] = {k: "" for k, _ in INSTITUTE_SEATING_COLUMN_SPECS}
state["inst_seating_manual_add"] = {k: "" for k, _ in INSTITUTE_SEATING_COLUMN_SPECS}

state["yearly_gaps"] = mt.load_yearly_gap_flags_from_db(mt.DB_FILE)

top_container = None      # enrollment-input area, mode-dependent
content_container = None  # mode body, set once the page is built
mode_buttons = {}
page_container = None     # top-level container render_page_body() clears/rebuilds each time


# =======================================================================
# MODE NAVIGATION (buttons are never disabled -- the sequence is
# communicated, not enforced; see the project decision to drop
# lock/unlock entirely). Scheme is no longer a concept here: only
# Seating Chart and Report still deal with scheme letters. Train,
# Extract, Course Codes, Offline Import, and Recheck just work over
# whatever the user pasted in.
# =======================================================================

def mark_complete_and_advance(mode_key):
    """Marks this mode complete and jumps to the next one in MODE_ORDER."""
    state["completed"].add(mode_key)
    idx = MODE_ORDER.index(mode_key)
    update_mode_buttons()
    if idx + 1 < len(MODE_ORDER):
        select_mode(MODE_ORDER[idx + 1])
    else:
        ui.notify("All modes complete!", type="positive")
        select_mode("seating")


def update_mode_buttons():
    """No enabling/disabling -- every mode button is always clickable.
    Just highlights whichever one is currently active."""
    for key, btn in mode_buttons.items():
        active = key == state["mode"]
        btn.props(f'color={"primary" if active else "grey-8"}')


def select_mode(mode_key):
    """No lock check -- the user is trusted to follow Train -> Extract ->
    Course Codes -> Report -> Recheck -> Offline Import in order; jumping
    ahead just won't have useful data yet (handled gracefully by each
    mode's own "no data" messaging)."""
    state["mode"] = mode_key
    update_mode_buttons()
    render_top_area()
    render_mode_content()


def enrollment_lines():
    """Non-blank, in-order enrollment numbers from the shared paste box."""
    return [line.strip() for line in state["enrollment_text"].splitlines() if line.strip()]


def train_enrollment_values():
    """Non-blank sample enrollment numbers entered for Train mode --
    one per line, any count, duplicates collapsed (keeping first
    occurrence's position) so pasting the same recommended list twice
    doesn't fetch the same enrollment repeatedly."""
    seen = set()
    out = []
    for line in state["train_enrollments_text"].splitlines():
        v = line.strip()
        if v and v not in seen:
            seen.add(v)
            out.append(v)
    return out


# =======================================================================
# CAPTCHA (web equivalent of get_captcha_from_popup)
# =======================================================================

async def ask_captcha_web(image_bytes):
    """Shows the captcha image + a text box inline in the Train mode UI
    (under the fetch log) instead of a popup, and waits for the user to
    submit (or cancel). Returns '' on cancel/empty.

    Wrapped in try/finally so that if this await is CANCELLED (e.g. the
    "Skip This Enrollment" or "Stop" button cancelling the enclosing
    fetch task -- see skip_current_enrollment()/stop_train_fetch() and
    their Extract/Recheck-Automatic counterparts), captcha_pending is
    still guaranteed to be cleared -- otherwise a stale captcha box would
    keep showing on screen even after the fetch it belonged to was
    abandoned."""
    b64 = base64.b64encode(image_bytes).decode("ascii")
    done = asyncio.Event()
    result = {"value": ""}

    state["captcha_pending"] = {"b64": b64, "done": done, "result": result}
    render_mode_content()

    try:
        await done.wait()
    finally:
        state["captcha_pending"] = None
    return result["value"]


def render_captcha_box(container):
    """Renders the pending captcha (image + input box) inline, inside
    whichever mode's fetching view is currently active. No-op if no
    captcha is pending."""
    pending = state.get("captcha_pending")
    if not pending:
        return

    def submit():
        pending["result"]["value"] = (captcha_input.value or "").strip()
        pending["done"].set()

    def cancel():
        pending["result"]["value"] = ""
        pending["done"].set()

    with container:
        with ui.card().classes("w-full items-center mt-2 border-2 border-primary"):
            ui.label("Captcha needed").classes("font-semibold")
            ui.image(f"data:image/png;base64,{pending['b64']}").classes("w-56")
            captcha_input = ui.input(label="Captcha").props("autofocus outlined").classes("w-48")
            captcha_input.on("keydown.enter", lambda e: submit())
            with ui.row():
                ui.button("Submit", on_click=submit).props("unelevated color=primary")
                ui.button("Cancel", on_click=cancel).props("flat")


async def web_fetch_result_html(session, enrollment, log_key="train_fetch_log"):
    """Web equivalent of msbte_tool.fetch_result_html: same HTTP/form
    steps, but the captcha is solved via ask_captcha_web instead of a
    tkinter popup, and blocking calls are offloaded with run.io_bound
    so the event loop stays free. Every network call has a timeout and
    logs a visible message on failure instead of hanging silently."""
    try:
        r = await run.io_bound(session.get, mt.MSBTE_URL, timeout=20)
    except Exception as e:
        _log(f"  Network error loading result page: {e}", log_key)
        return None

    soup = BeautifulSoup(r.text, "html.parser")

    try:
        viewstate = soup.find("input", {"name": "__VIEWSTATE"})["value"]
        eventvalidation = soup.find("input", {"name": "__EVENTVALIDATION"})["value"]
        viewstategenerator = soup.find("input", {"name": "__VIEWSTATEGENERATOR"})["value"]
        txt_captcha_cold = soup.find("input", {"name": "txtCaptchaCold"})["value"]
        txt_uri_no = soup.find("input", {"name": "txtUriNo"})["value"]
        txt_prev_uri_offset = soup.find("input", {"name": "txtPrevUriOffSet"})["value"]
        captcha_src = soup.find("img", {"id": "imgCaptcha"})["src"]
    except (TypeError, KeyError):
        _log("  Could not find the expected form fields on the result page (site layout may have changed, or the connection was blocked).", log_key)
        return None

    captcha_url = "https://result.msbte.ac.in/pcwebBTRes/" + captcha_src.replace("../", "")
    try:
        img_resp = await run.io_bound(session.get, captcha_url, timeout=20)
    except Exception as e:
        _log(f"  Network error loading captcha image: {e}", log_key)
        return None

    captcha = await ask_captcha_web(img_resp.content)
    if not captcha:
        return None

    payload = {
        "__VIEWSTATE": viewstate,
        "__VIEWSTATEGENERATOR": viewstategenerator,
        "__EVENTVALIDATION": eventvalidation,
        "ddlEnrollOrSeatNo": "2",
        "txtEnrollOrSeatNo": enrollment,
        "txtCaptchaHot": captcha,
        "txtCaptchaCold": txt_captcha_cold,
        "txtUriNo": txt_uri_no,
        "txtPrevUriOffSet": txt_prev_uri_offset,
        "txtAlert": "",
        "btnShowResult.x": "64",
        "btnShowResult.y": "13",
    }
    try:
        r2 = await run.io_bound(session.post, mt.MSBTE_URL, data=payload, timeout=20)
    except Exception as e:
        _log(f"  Network error submitting captcha: {e}", log_key)
        return None
    return r2.text


async def web_fetch_result_html_with_retry(session, enrollment, max_retries=mt.MAX_CAPTCHA_RETRIES, log_key="train_fetch_log"):
    attempt = 0
    while True:
        attempt += 1
        html = await web_fetch_result_html(session, enrollment, log_key)
        if not html:
            return None, attempt
        soup = BeautifulSoup(html, "html.parser")
        if soup.find_all("table"):
            return html, attempt
        if attempt > max_retries:
            return html, attempt


# =======================================================================
# TRAIN MODE - fetch phase
# =======================================================================

def _log(line, log_key="train_fetch_log"):
    state[log_key].append(line)
    render_mode_content()


def start_train_fetch():
    """Button handler -- validates input, resets the fetch screen, and
    launches the actual fetch loop as a separate cancellable asyncio
    Task (rather than awaiting it directly here) so Skip/Stop buttons
    rendered on the fetching screen can act on it while it's running."""
    vals = train_enrollment_values()
    if not vals:
        ui.notify("Enter at least one sample enrollment number first.", type="warning")
        return

    state["train_step"] = "fetching"
    state["train_fetch_log"] = []
    state["train_fetch_stop_requested"] = False
    state["train_fetch_current_task"] = None
    render_top_area()
    render_mode_content()

    asyncio.ensure_future(_train_fetch_worker(vals))


def skip_current_enrollment():
    """"Skip This Enrollment" -- cancels ONLY the current enrollment's
    fetch (whether it's stuck on the network call or waiting on a
    captcha that was never solved), letting the loop move straight on
    to the next enrollment. Does nothing (with a notice) if nothing is
    actually in flight right now."""
    task = state.get("train_fetch_current_task")
    if task is None or task.done():
        ui.notify("Nothing in progress to skip right now.", type="info")
        return
    task.cancel()
    ui.notify("Skipping current enrollment...", type="info")


def stop_train_fetch():
    """"Stop / Back to Input" -- aborts the ENTIRE batch: cancels
    whichever enrollment is currently in flight (so it doesn't have to
    finish/timeout first) and sets a flag the loop checks before moving
    to its next enrollment, so nothing further is attempted. Returns to
    the input step once the worker unwinds."""
    state["train_fetch_stop_requested"] = True
    task = state.get("train_fetch_current_task")
    if task is not None and not task.done():
        task.cancel()
    ui.notify("Stopping...", type="info")


async def _train_fetch_worker(vals):
    session = requests.Session()
    samples = {}

    for enr in vals:
        if state["train_fetch_stop_requested"]:
            _log("\nStopped by user.")
            break

        _log(f"Fetching {enr} ...")
        task = asyncio.ensure_future(
            web_fetch_result_html_with_retry(session, enr, log_key="train_fetch_log")
        )
        state["train_fetch_current_task"] = task
        try:
            html, attempts = await task
        except asyncio.CancelledError:
            _log(f"  Skipped {enr} (skipped by user).")
            state["train_fetch_current_task"] = None
            continue
        state["train_fetch_current_task"] = None

        if not html:
            _log(f"  Skipped {enr} (fetch/captcha cancelled).")
            continue

        soup = BeautifulSoup(html, "html.parser")
        tables = soup.find_all("table")
        chunks = mt.group_tables(tables)
        if not chunks:
            _log(f"  No result tables found for {enr}. Wrong enrollment number, or no result available.")
            continue

        found_labels = []
        for chunk in chunks:
            header_grid = mt.expand_table_grid(chunk[0])
            label = mt.extract_semester_label(header_grid)
            if not label:
                continue
            samples.setdefault(label, []).append((enr, chunk))
            found_labels.append(label)
        _log(f"  Found: {', '.join(found_labels) if found_labels else '(none)'}")

    state["train_fetch_current_task"] = None

    if state["train_fetch_stop_requested"]:
        ui.notify("Fetching stopped -- back to input.", type="info")
        state["train_step"] = "input"
        render_top_area()
        render_mode_content()
        return

    if not samples:
        _log("\nNo semester data collected from any enrollment number.")
        ui.notify(
            "Nothing to train -- no semester data collected. Check the enrollment "
            "number(s) and try again, or add different samples.",
            type="negative",
        )
        state["train_step"] = "input"
        render_top_area()
        render_mode_content()
        return

    state["train_samples"] = samples
    state["train_warnings"] = mt.cross_check_samples(samples)

    order = [l for l in mt.SEMESTER_NAMES if l in samples]
    order += [l for l in samples if l not in mt.SEMESTER_NAMES]
    state["train_order"] = order
    state["train_current_idx"] = 0
    state["train_mapping"] = {}
    state["train_collected"] = {key: [] for key, _ in mt.GROUPS}
    state["train_pending_rects"] = {}
    state["train_anchor"] = {}
    state["train_last_active_position"] = None

    settings = mt.load_report_settings(mt.DB_FILE)
    state["train_institute_name"] = settings.get("institute_name", "")
    state["train_institute_address"] = settings.get("institute_address", "")

    state["train_step"] = "select_ranges"
    render_top_area()
    render_mode_content()


# =======================================================================
# TRAIN MODE - range selection phase
# =======================================================================

CELL_BG_CLASSES = "bg-white bg-amber-300 bg-blue-200 bg-green-100 bg-green-200 bg-purple-200 bg-orange-100"


def set_cell_bg(position, r, c, bg_class):
    cell = state["train_cell_elements"].get((position, r, c))
    if cell is not None:
        cell.classes(remove=CELL_BG_CLASSES, add=bg_class)


def set_group_icon(group_key, visible):
    icon = state["train_group_icons"].get(group_key)
    if icon is not None:
        icon.set_visibility(visible)


def _entry_to_collected(entry):
    """Turn a saved semester's flat-groups entry (as save_semester_ranges
    writes it) back into the state["train_collected"] tuple format, so a
    previous semester's ranges can be re-applied to the current one."""
    collected = {key: [] for key, _ in mt.GROUPS}
    for group_key, spec in entry.items():
        for rng in spec.get("ranges", []):
            collected[group_key].append((
                rng["position_in_group"], rng["row_start"], rng["row_end"],
                rng["col_start"], rng["col_end"], rng["expected_num_cols"],
            ))
    return collected


def _paint_collected_groups(color):
    for rects in state["train_collected"].values():
        for (p, r0, r1, c0, c1, _num_cols) in rects:
            for rr in range(r0, r1 + 1):
                for cc in range(c0, c1 + 1):
                    set_cell_bg(p, rr, cc, color)


def _previous_ranges_entry():
    """The saved flat-groups entry for the semester trained right before
    the current one, if any -- the source for "import same addresses"."""
    idx = state["train_current_idx"]
    if idx == 0:
        return None, None
    prev_label = state["train_order"][idx - 1]
    return prev_label, state["train_mapping"].get(prev_label)


def toggle_import_previous(checked):
    """Checkbox handler -- re-imports (and re-paints purple) or clears
    back to blank, live, without re-rendering the whole step."""
    state["train_import_checked"] = checked
    _, prev_entry = _previous_ranges_entry()
    if checked and prev_entry:
        state["train_collected"] = _entry_to_collected(prev_entry)
        for key, _ in NON_SUBJECT_GROUPS:
            set_group_icon(key, bool(state["train_collected"][key]))
        _paint_collected_groups("bg-purple-200")
    else:
        _paint_collected_groups("bg-white")
        state["train_collected"] = {key: [] for key, _ in mt.GROUPS}
        for key, _ in NON_SUBJECT_GROUPS:
            set_group_icon(key, False)


async def on_cell_mousedown(position, r, c):
    """Start of a drag-select -- just remembers the anchor and highlights
    that one cell directly (no re-render of anything else)."""
    state["train_anchor"][position] = (r, c)
    set_cell_bg(position, r, c, "bg-amber-300")


async def on_cell_mouseup(position, r, c):
    """End of a drag-select (or a plain click, which is just a drag of
    zero distance) -- commits the rectangle from anchor to here and
    highlights just those cells. Nothing is rebuilt, so scroll position
    in either panel is untouched.

    A plain click (no drag) on a cell that's already pending as its own
    single-cell selection toggles it back OFF instead of adding a
    duplicate -- lets a wrong click be undone by clicking the same wrong
    cell again, without needing a separate undo control."""
    anchor = state["train_anchor"].pop(position, None)
    if anchor is None:
        return
    r0, c0 = anchor
    rect = (min(r0, r), max(r0, r), min(c0, c), max(c0, c))
    pending = state["train_pending_rects"].setdefault(position, [])
    if rect[0] == rect[1] and rect[2] == rect[3] and rect in pending:
        pending.remove(rect)
        set_cell_bg(position, r, c, "bg-white")
        return
    pending.append(rect)
    state["train_last_active_position"] = position
    for rr in range(rect[0], rect[1] + 1):
        for cc in range(rect[2], rect[3] + 1):
            set_cell_bg(position, rr, cc, "bg-blue-200")


async def add_to_group(group_key):
    p = state["train_last_active_position"]
    pending = state["train_pending_rects"].get(p) if p is not None else None
    if p is None or not pending:
        ui.notify(
            "Drag across (or click) a cell in a table first to mark a selection.",
            type="warning",
        )
        return
    label = state["train_order"][state["train_current_idx"]]
    chunk = state["train_samples"][label][0][1]
    grid_data = mt.expand_table_grid(chunk[p])
    num_cols = max((len(row) for row in grid_data), default=0)
    for (r0, r1, c0, c1) in pending:
        state["train_collected"][group_key].append((p, r0, r1, c0, c1, num_cols))
        for rr in range(r0, r1 + 1):
            for cc in range(c0, c1 + 1):
                set_cell_bg(p, rr, cc, "bg-white")
    state["train_pending_rects"][p] = []
    set_group_icon(group_key, True)


async def clear_group(group_key):
    for (p, r0, r1, c0, c1, _num_cols) in state["train_collected"][group_key]:
        for rr in range(r0, r1 + 1):
            for cc in range(c0, c1 + 1):
                set_cell_bg(p, rr, cc, "bg-white")
    state["train_collected"][group_key] = []
    set_group_icon(group_key, False)


def save_semester_ranges():
    label = state["train_order"][state["train_current_idx"]]
    collected = state["train_collected"]

    entry = {}
    for group_key, _ in NON_SUBJECT_GROUPS:
        rects = collected[group_key]
        if not rects:
            continue
        entry[group_key] = {
            "ranges": [
                {
                    "position_in_group": pos, "row_start": r0, "row_end": r1,
                    "col_start": c0, "col_end": c1, "expected_num_cols": num_cols,
                }
                for (pos, r0, r1, c0, c1, num_cols) in rects
            ]
        }

    name = state["train_institute_name"].strip()
    address = state["train_institute_address"].strip()
    if name or address:
        mt.save_report_settings({"institute_name": name, "institute_address": address}, mt.DB_FILE)

    if entry:
        state["train_mapping"][label] = entry
        _write_mapping_merged({label: entry})
        ui.notify(f"Ranges saved for {label}: {', '.join(entry.keys())}", type="positive")
    else:
        ui.notify(f"No ranges selected for {label} -- skipped.", type="warning")

    # Subjects/components are trained next, via the one-drag wizard,
    # rather than as more flat ranges here -- see SUBJECT_TABLE_GROUP_KEYS
    # above.
    state["train_collected"] = {key: [] for key, _ in mt.GROUPS}
    state["train_pending_rects"] = {}
    state["train_anchor"] = {}
    state["train_last_active_position"] = None

    state["train_wizard_anchor"] = None
    state["train_wizard_pending"] = None
    state["train_whole_table_drag"] = None
    state["train_subjects_drag"] = None
    state["train_subjects_preview"] = []
    state["train_orientation"] = None
    state["train_level_count"] = None
    state["train_level_drags"] = [None] * mt.MAX_TEMPLATE_LEVELS
    state["train_values_drag"] = None

    state["train_step"] = "subjectwise_panel"
    render_top_area()
    render_mode_content()


def _write_mapping_merged(new_entries):
    """Merge new semester entries into the session's layout_mapping.json
    (never overwrites semesters trained earlier)."""
    path = mt.MAPPING_FILE
    os.makedirs(os.path.dirname(path) or ".", exist_ok=True)
    existing = {}
    if os.path.exists(path):
        try:
            with open(path, encoding="utf-8") as f:
                existing = json.load(f) or {}
        except (json.JSONDecodeError, OSError):
            existing = {}
    existing.update(new_entries)
    with open(path, "w", encoding="utf-8") as f:
        json.dump(existing, f, indent=2, ensure_ascii=False)


def finalize_training():
    mapping = state["train_mapping"]
    _write_mapping_merged(mapping)

    for label in state["train_order"]:
        if label not in mapping:
            continue
        sample_enr, sample_chunk = state["train_samples"][label][0]
        sample_extracted, _ = mt.apply_mapping_to_chunk(sample_chunk, label, mapping[label], sample_enr)
        mt.save_semester_headings_to_db(sample_extracted, label, mt.DB_FILE)

    state["train_step"] = "done"
    render_top_area()
    render_mode_content()


def render_grid(container, position, grid_data, mousedown_handler=None, mouseup_handler=None,
                 highlight_rows=None):
    """highlight_rows, if given, is a (row_start, row_end) band (e.g. the
    active subject's own rows during Step 2) painted a light background
    so it's obvious at a glance which rows belong to it -- purely visual,
    doesn't affect selection."""
    down = mousedown_handler or on_cell_mousedown
    up = mouseup_handler or on_cell_mouseup
    num_cols = max((len(row) for row in grid_data), default=0)
    with container:
        ui.label(f"Table {position + 1} ({len(grid_data)} rows x {num_cols} cols)").classes(
            "text-xs font-semibold mt-2"
        )
        with ui.element("table").classes("border-collapse mb-2"):
            for r, row in enumerate(grid_data):
                with ui.element("tr"):
                    for c in range(num_cols):
                        val = row[c] if c < len(row) else ""
                        base_bg = "bg-white"
                        if highlight_rows is not None and highlight_rows[0] <= r <= highlight_rows[1]:
                            base_bg = "bg-orange-100"
                        cell = ui.element("td").classes(
                            f"border px-1 py-0.5 cursor-pointer select-none {base_bg}"
                        ).style(
                            "font-size: 10px; line-height: 1.2; max-width: 110px; "
                            "white-space: normal; word-break: break-word;"
                        )
                        with cell:
                            ui.label(val if val else "\u00a0").style("word-break: break-word;")
                        cell.on("mousedown", lambda e, rr=r, cc=c, p=position: down(p, rr, cc))
                        cell.on("mouseup", lambda e, rr=r, cc=c, p=position: up(p, rr, cc))
                        state["train_cell_elements"][(position, r, c)] = cell
                        state["train_cell_text"][(position, r, c)] = val



def flatten_rects_to_cells(rects):
    """[(position, r0, r1, c0, c1), ...] -> [(position, r, c), ...], row-major
    within each rect, in the order the rects were added. A single-column
    drag across several subjects' rows flattens into one cell per row, top
    to bottom -- exactly "bulk select down a column" for K-scheme-style
    sheets where a component is a fixed column across every subject."""
    cells = []
    for (position, r0, r1, c0, c1) in rects:
        for r in range(r0, r1 + 1):
            for c in range(c0, c1 + 1):
                cells.append((position, r, c))
    return cells


def flatten_rects_to_cells(rects):
    """[(position, r0, r1, c0, c1), ...] -> [(position, r, c), ...], row-major
    within each rect, in the order the rects were added. Still used by
    the flat identity/summary range selector (Step "select_ranges")."""
    cells = []
    for (position, r0, r1, c0, c1) in rects:
        for r in range(r0, r1 + 1):
            for c in range(c0, c1 + 1):
                cells.append((position, r, c))
    return cells


# =======================================================================
# Subject-wise trainer v3: ONE drag per concept, done in this exact order:
#   Whole Table -> Subjects -> Level 1 -> Level 2 -> ... -> Max+Obtained
#
# Order: Whole Table -> Subjects -> [Common/Varies choice] -> Level 1 ->
#   Level 2 -> ... -> Max+Obtained
#
# No per-subject or per-leaf clicking anywhere. Orientation (Common =
# K-scheme-style shared header ROW per level, Varies = I-scheme-style
# per-row label COLUMN per level, block height varying per subject) is
# asked explicitly ONCE right after Subjects is confirmed, and applies
# to every Level drag for that semester.
# The component tree, per-subject applicability, and every Max/Obtained
# cell position are all derived automatically from these few drags and
# saved into the exact same subjects/component_template/
# subject_node_values (or subjectwise_vertical_roles, for vertical)
# tables the old per-cell trainer used -- so every report function keeps
# working completely unchanged.

async def on_wizard_cell_mousedown(position, r, c):
    state["train_wizard_anchor"] = (position, r, c)
    set_cell_bg(position, r, c, "bg-amber-300")


async def on_wizard_cell_mouseup(position, r, c):
    anchor = state["train_wizard_anchor"]
    if anchor is None or anchor[0] != position:
        return
    _, r0, c0 = anchor
    state["train_wizard_anchor"] = None
    state["train_wizard_pending"] = {
        "position": position,
        "row_start": min(r0, r), "row_end": max(r0, r),
        "col_start": min(c0, c), "col_end": max(c0, c),
    }
    render_mode_content()


def _clear_wizard_pending():
    state["train_wizard_pending"] = None
    state["train_wizard_anchor"] = None


def _paint_pending_drag():
    """Highlights the current train_wizard_pending rect blue -- called
    right after render_grid() draws everything white."""
    rect = state["train_wizard_pending"]
    if not rect:
        return
    for r in range(rect["row_start"], rect["row_end"] + 1):
        for c in range(rect["col_start"], rect["col_end"] + 1):
            set_cell_bg(rect["position"], r, c, "bg-blue-200")


def _sample_chunk():
    label = state["train_order"][state["train_current_idx"]]
    sample_enr, chunk = state["train_samples"][label][0]
    return label, sample_enr, chunk


def render_drag_step(container, step_title, instructions, on_confirm, confirm_label="Confirm",
                      extra_top=None, on_back=None):
    """Shared scaffold for every one-drag step: instructions, a live
    "Selected: table X, rows A-B, cols C-D" readout once a drag is made,
    Confirm/Redo, and the sample table itself below. `extra_top`, if
    given, is called with the card still open, right after the
    instructions -- used for the Level step's "already confirmed" list
    and "Done adding levels" button. `on_back`, if given, renders a
    "Back" button that returns to the previous wizard step."""
    label, sample_enr, chunk = _sample_chunk()
    with container:
        with ui.card().classes("w-full").style("padding: 6px 14px;"):
            with ui.row().classes("items-center gap-3 no-wrap"):
                ui.label(f"{label}").classes("text-sm font-bold")
                ui.label(step_title).classes("text-xs text-blue-700 font-semibold")
                ui.label(f"(sample: {sample_enr})").classes("text-xs text-gray-500")
            ui.label(instructions).classes("text-xs text-gray-500 mt-1")
            if extra_top:
                extra_top()
            pending = state["train_wizard_pending"]
            with ui.row().classes("gap-2 mt-2 items-center"):
                if on_back:
                    ui.button("Back", icon="arrow_back", on_click=on_back).props("outline dense")
                if pending:
                    ui.label(
                        f"Selected: table {pending['position'] + 1}, "
                        f"rows {pending['row_start']}-{pending['row_end']}, "
                        f"cols {pending['col_start']}-{pending['col_end']}"
                    ).classes("text-xs text-blue-700 font-semibold")
                    ui.button(confirm_label, icon="check", on_click=on_confirm).props(
                        "unelevated color=primary dense"
                    )
                    ui.button("Redo this drag", on_click=lambda: (_clear_wizard_pending(), render_mode_content())).props(
                        "outline dense"
                    )
                else:
                    ui.label("Drag across the relevant cells now.").classes("text-xs text-gray-400 italic")

        with ui.column().classes("gap-1 overflow-y-auto overflow-x-hidden mt-3").style(
            "max-height: 72vh"
        ).props('id=trainer-grid-scroll'):
            state["train_cell_elements"] = {}
            for pos, table in enumerate(chunk):
                grid_data = mt.expand_table_grid(table)
                grid_col = ui.column().classes("gap-0 w-full")
                render_grid(grid_col, pos, grid_data,
                            mousedown_handler=on_wizard_cell_mousedown,
                            mouseup_handler=on_wizard_cell_mouseup)
    _paint_pending_drag()


MAX_LEVELS = mt.MAX_TEMPLATE_LEVELS  # all Level cards are pre-built up to this many, shown/hidden
                                      # rather than added/removed, so toggling the level-count
                                      # dropdown never rebuilds (and never scrolls) the sidebar.


def _group_rect(kind):
    if kind == "whole_table":
        return state["train_whole_table_drag"]
    if kind == "subjects":
        return state["train_subjects_drag"]
    if kind == "max_obt":
        return state["train_values_drag"]
    if kind.startswith("level_"):
        i = int(kind.split("_", 1)[1])
        drags = state["train_level_drags"]
        return drags[i] if i < len(drags) else None
    return None


def _set_group_rect(kind, rect):
    if kind == "whole_table":
        state["train_whole_table_drag"] = rect
    elif kind == "subjects":
        state["train_subjects_drag"] = rect
    elif kind == "max_obt":
        state["train_values_drag"] = rect
    elif kind.startswith("level_"):
        i = int(kind.split("_", 1)[1])
        state["train_level_drags"][i] = rect


def _paint_rect(rect, color):
    if not rect:
        return
    for rr in range(rect["row_start"], rect["row_end"] + 1):
        for cc in range(rect["col_start"], rect["col_end"] + 1):
            set_cell_bg(rect["position"], rr, cc, color)


def _paint_subjectwise_groups():
    """Repaint every already-confirmed group green -- called once right
    after the panel's table is first drawn, so a semester re-entered
    mid-training (e.g. via Back) shows its existing selections."""
    for kind in ["whole_table", "subjects", "max_obt"] + [f"level_{i}" for i in range(MAX_LEVELS)]:
        _paint_rect(_group_rect(kind), "bg-green-100")


def render_subjectwise_panel(container):
    label, sample_enr, chunk = _sample_chunk()

    state["train_cell_elements"] = {}
    state["train_group_icons"] = {}
    state["train_pending_rects"] = {}
    state["train_anchor"] = {}
    state["train_last_active_position"] = None
    state["train_level_card_containers"] = {}
    state["train_level_hint_labels"] = {}
    state["train_subjects_count_label"] = None

    with container:
        with ui.card().classes("w-full").style("padding: 6px 14px;"):
            with ui.row().classes("items-center gap-3 no-wrap"):
                ui.button("Back", icon="arrow_back", on_click=back_to_select_ranges).props("outline dense")
                ui.label(f"{label}").classes("text-sm font-bold")
                ui.label("Subjects, Levels && Max/Obtained").classes("text-xs text-blue-700 font-semibold")
                ui.label(f"(sample: {sample_enr})").classes("text-xs text-gray-500")
            with ui.expansion("How this works", icon="help_outline").classes("w-full text-xs mt-1"):
                ui.label(
                    'Click/drag a range in the table below, then click "Add" under the matching '
                    'card on the left -- same idea as the previous screen. Fill in Whole Table and '
                    'Subjects first, then pick Common/Varied and how many Levels, then each Level '
                    'card and Max+Obtained, then Continue at the bottom.'
                ).classes("text-xs text-gray-500")

        with ui.row().classes("w-full gap-4 items-start no-wrap mt-4"):
            with ui.column().classes("w-80 gap-2 flex-shrink-0 overflow-y-auto").style(
                "max-height: 80vh"
            ).props('id=trainer-sidebar-scroll'):

                _render_group_card(
                    "whole_table", "1. Whole Table",
                    "Drag across the ENTIRE marks table -- every header row and every subject's row.",
                )
                _render_group_card(
                    "subjects", "2. Subjects",
                    "Drag straight down the column with each subject's name (data rows only, skip "
                    "header rows).",
                )

                with ui.card().classes("w-full"):
                    ui.label("3. Level layout").classes("text-sm font-semibold")
                    ui.label(
                        "Common: one shared header row, same for every subject. Varies per subject: "
                        "a column, with a per-row label (block height can differ per subject)."
                    ).classes("text-xs text-gray-500 mt-1")
                    ui.radio(
                        {"horizontal": "Common", "vertical": "Varies per subject"},
                        value=state["train_orientation"],
                        on_change=lambda e: set_orientation(e.value),
                    ).props("inline")

                with ui.card().classes("w-full"):
                    ui.label("4. Number of Levels").classes("text-sm font-semibold")
                    ui.label(
                        "E.g. TH \u2192 FA \u2192 (Max/Obtained) is 2 levels above the marks "
                        "themselves. Changing this clears any Level selections already made below."
                    ).classes("text-xs text-gray-500 mt-1")
                    ui.select(
                        {n: str(n) for n in range(1, MAX_LEVELS + 1)},
                        value=state["train_level_count"],
                        on_change=lambda e: set_level_count(e.value),
                    ).classes("w-full mt-1")

                for i in range(MAX_LEVELS):
                    kind = f"level_{i}"
                    card = ui.card().classes("w-full")
                    card.set_visibility(bool(state["train_level_count"]) and i < state["train_level_count"])
                    state["train_level_card_containers"][i] = card
                    with card:
                        with ui.row().classes("items-center justify-between w-full"):
                            ui.label(f"Level {i + 1}").classes("text-sm font-semibold")
                            icon = ui.icon("check_circle", color="green")
                            icon.set_visibility(_group_rect(kind) is not None)
                            state["train_group_icons"][kind] = icon
                        hint_label = ui.label(_level_hint_text(i)).classes("text-xs text-gray-500")
                        state["train_level_hint_labels"][i] = hint_label
                        with ui.row().classes("gap-2 w-full mt-1"):
                            ui.button("Add", on_click=lambda k=kind: add_subjectwise_group(k)).props(
                                "dense outline"
                            ).classes("flex-grow")
                            ui.button("Clear", on_click=lambda k=kind: clear_subjectwise_group(k)).props(
                                "dense outline color=grey"
                            ).classes("flex-grow")

                _render_group_card(
                    "max_obt", "5. Max + Obtained",
                    "Drag the Max and Obtained columns/cells together, in one motion -- a Min "
                    "Marks column in between (if any) is detected and skipped automatically.",
                )

                ui.button(
                    "Save && Train Next Semester \u2192", icon="arrow_forward",
                    on_click=finish_subjectwise_training,
                ).classes("w-full mt-2").props("unelevated color=primary")

            with ui.column().classes("gap-1 overflow-y-auto overflow-x-hidden flex-grow").style(
                "max-height: 80vh"
            ).props('id=trainer-grid-scroll'):
                for pos, table in enumerate(chunk):
                    grid_data = mt.expand_table_grid(table)
                    grid_col = ui.column().classes("gap-0 w-full")
                    render_grid(grid_col, pos, grid_data)

    _paint_subjectwise_groups()


def _level_hint_text(i):
    if state["train_orientation"] == "vertical":
        return (f"Drag straight down the COLUMN for Level {i + 1} -- the column with this level's "
                f"per-row label (e.g. TH / PR for Level 1), spanning the same rows as Subjects.")
    return (f"Drag across the HEADER ROW for Level {i + 1} -- the row with this level's labels "
            f"(e.g. THEORY / PRACTICALS / SLA for Level 1), spanning every value column. Every "
            f"subject shares this same header, so this is one drag total, not one per subject.")


def _render_group_card(kind, title, hint):
    with ui.card().classes("w-full"):
        with ui.row().classes("items-center justify-between w-full"):
            ui.label(title).classes("text-sm font-semibold")
            icon = ui.icon("check_circle", color="green")
            icon.set_visibility(_group_rect(kind) is not None)
            state["train_group_icons"][kind] = icon
        ui.label(hint).classes("text-xs text-gray-500")
        if kind == "subjects":
            count_label = ui.label(
                f"{len(state['train_subjects_preview'])} subject(s) found" if state["train_subjects_preview"] else ""
            ).classes("text-xs text-green-700 mt-1")
            state["train_subjects_count_label"] = count_label
        with ui.row().classes("gap-2 w-full mt-1"):
            ui.button("Add", on_click=lambda k=kind: add_subjectwise_group(k)).props(
                "dense outline"
            ).classes("flex-grow")
            ui.button("Clear", on_click=lambda k=kind: clear_subjectwise_group(k)).props(
                "dense outline color=grey"
            ).classes("flex-grow")


def back_to_select_ranges():
    state["train_step"] = "select_ranges"
    render_top_area()
    render_mode_content()


def set_orientation(choice):
    """Switching Common <-> Varied changes what a Level drag even means
    (a header row vs. a column), so any already-confirmed Level
    selections are invalidated -- clear and repaint them, then just
    update each level card's hint text and the radio's own state, no
    rebuild of the sidebar or table (so scroll position is untouched)."""
    state["train_orientation"] = choice
    for i in range(MAX_LEVELS):
        rect = _group_rect(f"level_{i}")
        if rect:
            _paint_rect(rect, "bg-white")
        state["train_level_drags"][i] = None
        icon = state["train_group_icons"].get(f"level_{i}")
        if icon is not None:
            icon.set_visibility(False)
        hint_label = state["train_level_hint_labels"].get(i)
        if hint_label is not None:
            hint_label.set_text(_level_hint_text(i))


def set_level_count(n):
    """Any change here clears every existing Level selection (the
    structure changed), then just shows/hides the pre-built Level cards
    -- no rebuild, so scroll position is untouched."""
    for i in range(MAX_LEVELS):
        rect = _group_rect(f"level_{i}")
        if rect:
            _paint_rect(rect, "bg-white")
        state["train_level_drags"][i] = None
        icon = state["train_group_icons"].get(f"level_{i}")
        if icon is not None:
            icon.set_visibility(False)
    state["train_level_count"] = n
    for i in range(MAX_LEVELS):
        card = state["train_level_card_containers"].get(i)
        if card is not None:
            card.set_visibility(i < n)


def add_subjectwise_group(kind):
    p = state["train_last_active_position"]
    pending = state["train_pending_rects"].get(p) if p is not None else None
    if p is None or not pending:
        ui.notify("Drag across (or click) a cell in a table first.", type="warning")
        return
    r0, r1, c0, c1 = pending[-1]
    rect = {"position": p, "row_start": r0, "row_end": r1, "col_start": c0, "col_end": c1}

    if kind == "subjects":
        _, _, chunk = _sample_chunk()
        if p >= len(chunk):
            ui.notify("That table position looks out of range -- try again.", type="negative")
            return
        grid = mt.expand_table_grid(chunk[p])
        subjects = mt.derive_subjects_from_drag(grid, r0, r1, c0)
        if not subjects:
            ui.notify("No subject names found in that drag -- make sure it's the column with each "
                       "subject's name, on data rows only.", type="warning")
            return
        state["train_subjects_preview"] = subjects
        count_label = state.get("train_subjects_count_label")
        if count_label is not None:
            count_label.set_text(f"{len(subjects)} subject(s) found")

    _set_group_rect(kind, rect)

    for (rr0, rr1, cc0, cc1) in pending:
        for rr in range(rr0, rr1 + 1):
            for cc in range(cc0, cc1 + 1):
                set_cell_bg(p, rr, cc, "bg-white")
    state["train_pending_rects"][p] = []
    _paint_rect(rect, "bg-green-100")

    icon = state["train_group_icons"].get(kind)
    if icon is not None:
        icon.set_visibility(True)


def clear_subjectwise_group(kind):
    rect = _group_rect(kind)
    if rect:
        _paint_rect(rect, "bg-white")
    _set_group_rect(kind, None)
    if kind == "subjects":
        state["train_subjects_preview"] = []
        count_label = state.get("train_subjects_count_label")
        if count_label is not None:
            count_label.set_text("")
    icon = state["train_group_icons"].get(kind)
    if icon is not None:
        icon.set_visibility(False)


def finish_subjectwise_training():
    missing = []
    if not state["train_whole_table_drag"]:
        missing.append("Whole Table")
    if not state["train_subjects_drag"] or not state["train_subjects_preview"]:
        missing.append("Subjects")
    if not state["train_orientation"]:
        missing.append("Level layout (Common/Varied)")
    level_count = state["train_level_count"]
    if not level_count:
        missing.append("Number of Levels")
    else:
        for i in range(level_count):
            if not _group_rect(f"level_{i}"):
                missing.append(f"Level {i + 1}")
    if not state["train_values_drag"]:
        missing.append("Max + Obtained")
    if missing:
        ui.notify("Still needed: " + ", ".join(missing), type="warning")
        return

    label, sample_enr, chunk = _sample_chunk()
    subjects_drag = state["train_subjects_drag"]
    values_drag = state["train_values_drag"]
    level_drags = state["train_level_drags"][:level_count]
    if values_drag["position"] != subjects_drag["position"]:
        ui.notify("Max + Obtained is on a different table than Subjects/Levels were -- drag on "
                   "the same table.", type="negative")
        return

    grid = mt.expand_table_grid(chunk[subjects_drag["position"]])
    try:
        if state["train_orientation"] == "horizontal":
            result = mt.finalize_subjectwise_training_horizontal(
                label, grid, subjects_drag["position"],
                subjects_drag=subjects_drag, level_drags=level_drags,
                values_drag=values_drag, db_path=mt.DB_FILE,
            )
        else:
            result = mt.finalize_subjectwise_training_vertical(
                label, grid, subjects_drag["position"],
                subjects_drag=subjects_drag, level_drags=level_drags,
                values_drag=values_drag, db_path=mt.DB_FILE,
            )
    except ValueError as e:
        ui.notify(str(e), type="negative")
        return

    state["train_last_trained_subjects"] = result["subjects"]
    state["train_last_trained_nodes"] = result["nodes"]

    # Read the SAME sample page back through the extractor we just
    # trained -- this is exactly what a real student's page will go
    # through, so showing these values (not just the structure) is the
    # real proof the right cells were picked, not just that a tree shape
    # was parsed. Pass the FULL chunk (not sliced to one table) since the
    # trained position/roles are absolute indices into the original
    # multi-table chunk -- slicing here would make that index point past
    # the end whenever the marks table isn't the very first table.
    if state["train_orientation"] == "horizontal":
        preview_records, preview_review = mt.extract_subjectwise_from_chunk(chunk, label, sample_enr, mt.DB_FILE)
    else:
        preview_records, preview_review = mt.extract_subjectwise_vertical_from_chunk(chunk, label, sample_enr, mt.DB_FILE)
    state["train_preview_records"] = preview_records
    state["train_preview_review"] = preview_review
    state["train_preview_enr"] = sample_enr

    state["train_step"] = "wizard_done"
    render_top_area()
    render_mode_content()


# --- Per-semester summary + advance --------------------------------------

def build_training_preview_tree(subjects, nodes, records):
    """[{'id','label','children':[...]}] for ui.tree(): one branch per
    subject, then down through the component levels, ending in a leaf
    labelled with the ACTUAL Max/Obtained values read back from the
    sample page -- not just the structure, the real numbers, so a wrong
    cell shows up immediately instead of only surfacing later in a report."""
    nodes_by_id = {n["node_id"]: n for n in nodes}
    values_by_key = {}  # (subject_index, node_id) -> {"max": v, "obtained": v}
    for r in records:
        values_by_key.setdefault((r["subject_index"], r["node_id"]), {})[r["role"]] = r["value"]

    def children_of(parent_id, subject_index):
        kids = [n for n in nodes if n["parent_id"] == parent_id]
        out = []
        for n in kids:
            grandchildren = children_of(n["node_id"], subject_index)
            if grandchildren:
                out.append({"id": f"s{subject_index}-n{n['node_id']}", "label": n["label"],
                            "children": grandchildren})
            else:
                vals = values_by_key.get((subject_index, n["node_id"]))
                if vals is None:
                    continue  # this subject never had this leaf (blank/dash on the sample) -- omit
                out.append({
                    "id": f"s{subject_index}-n{n['node_id']}",
                    "label": f"{n['label']}  (Max {vals.get('max', '?')} / Obt {vals.get('obtained', '?')})",
                })
        return out

    tree = []
    for s in subjects:
        tree.append({
            "id": f"s{s['subject_index']}",
            "label": s["subject_name"],
            "children": children_of(None, s["subject_index"]),
        })
    return tree


def render_wizard_done(container):
    label = state["train_order"][state["train_current_idx"]]
    subjects = state["train_last_trained_subjects"]
    nodes = state["train_last_trained_nodes"]
    records = state["train_preview_records"]
    leaves = mt.leaf_nodes(nodes)
    is_last = state["train_current_idx"] >= len(state["train_order"]) - 1
    tree_data = build_training_preview_tree(subjects, nodes, records)
    all_node_ids = [n["id"] for n in tree_data]  # subject-level ids, for a one-click expand-all
    with container:
        with ui.card().classes("w-full"):
            ui.label(f"{label} -- trained!").classes("text-lg font-bold text-green-700")
            ui.label(
                f"{len(subjects)} subject(s) found, up to {len(leaves)} component(s) each "
                f"({state['train_orientation']} layout). Values below are read from the sample "
                f"page ({state['train_preview_enr']}) using exactly what was just trained -- check "
                f"they match the actual sheet before continuing."
            ).classes("text-sm mt-1")
            with ui.row().classes("gap-2 mt-2 flex-wrap"):
                for s in subjects:
                    ui.badge(s["subject_name"]).props("outline color=primary")

            preview_review = state.get("train_preview_review") or []
            if preview_review:
                with ui.element("div").classes(
                    "bg-red-50 border border-red-400 rounded p-2 mt-3"
                ):
                    ui.label(
                        f"\u26a0 {len(preview_review)} row(s)/subject(s) on the sample page didn't "
                        f"match this training -- this is why values are missing above:"
                    ).classes("text-sm font-bold text-red-700")
                    for item in preview_review:
                        ui.label(item.get("reason", "")).classes("text-xs text-red-700 mt-1")

            with ui.row().classes("gap-2 mt-4 items-center"):
                ui.button("Back", icon="arrow_back", on_click=back_to_values_from_done).props("outline dense")
                ui.button(
                    "Finish Training \u2192" if is_last else "Continue to Next Semester \u2192",
                    icon="arrow_forward", on_click=advance_after_subjectwise_training,
                ).props("unelevated color=primary")

        with ui.card().classes("w-full mt-3"):
            ui.label("Trained structure + sample values").classes("text-sm font-semibold")
            tree = ui.tree(tree_data, label_key="label", node_key="id")
            tree.expand()
            with ui.row().classes("gap-2 mt-2"):
                ui.button("Expand all", on_click=lambda: tree.expand()).props("dense outline")
                ui.button("Collapse all", on_click=lambda: tree.collapse()).props("dense outline")


def back_to_values_from_done():
    state["train_step"] = "subjectwise_panel"
    render_top_area()
    render_mode_content()


def advance_after_subjectwise_training():
    state["train_current_idx"] += 1
    state["train_whole_table_drag"] = None
    state["train_subjects_drag"] = None
    state["train_subjects_preview"] = []
    state["train_orientation"] = None
    state["train_level_count"] = None
    state["train_level_drags"] = [None] * mt.MAX_TEMPLATE_LEVELS
    state["train_values_drag"] = None
    state["train_last_trained_subjects"] = []
    state["train_last_trained_nodes"] = []
    state["train_preview_records"] = []
    state["train_preview_review"] = []
    state["train_preview_enr"] = None
    _clear_wizard_pending()

    if state["train_current_idx"] >= len(state["train_order"]):
        finalize_training()
    else:
        state["train_step"] = "select_ranges"
        render_top_area()
        render_mode_content()



def render_train_input(container):
    with container:
        with ui.card().classes("w-full"):
            ui.label("Train").classes("text-xl font-bold")
            ui.label(MODE_DESCRIPTIONS["train"]).classes("text-sm text-gray-600")
            ui.separator()

            trained = mt.list_subjectwise_semesters(mt.DB_FILE)
            if trained:
                trained_sorted = [l for l in mt.SEMESTER_NAMES if l in trained] + [
                    l for l in trained if l not in mt.SEMESTER_NAMES
                ]
                with ui.element("div").classes("bg-blue-50 border border-blue-300 rounded p-2 mt-1"):
                    ui.label(
                        f"{len(trained_sorted)} semester(s) already trained for this scheme:"
                    ).classes("text-sm font-semibold text-blue-800")
                    with ui.row().classes("gap-2 flex-wrap mt-1"):
                        for l in trained_sorted:
                            ui.chip(l.title(), icon="check_circle", color="blue-2")
                    ui.label(
                        "Want to train more? Enter new sample enrollment number(s) above and "
                        "click \"Fetch These\" -- any NEW semester found gets added; an "
                        "already-trained semester listed above is simply re-confirmed, not lost."
                    ).classes("text-xs text-blue-700 mt-1")

            vals = train_enrollment_values()
            if vals:
                ui.label(f"{len(vals)} sample enrollment(s) entered:").classes("text-sm mt-3 font-medium")
                with ui.row().classes("gap-2 flex-wrap mt-1"):
                    for v in vals:
                        ui.chip(v, icon="badge")
            else:
                ui.label("No sample enrollment numbers entered yet.").classes("text-gray-400 italic mt-4")
            ui.label('Click "Fetch These" above once you\'ve entered your samples.').classes(
                "text-xs text-gray-400 mt-4"
            )


def render_fetching(container):
    with container:
        with ui.card().classes("w-full"):
            ui.label("Fetching sample results...").classes("text-lg font-semibold")
            ui.label("Solve each captcha as it appears below.").classes("text-xs text-gray-500")
            with ui.row().classes("gap-2 mt-2"):
                ui.button(
                    "Skip This Enrollment", icon="skip_next", on_click=skip_current_enrollment,
                ).props("dense outline")
                ui.button(
                    "Stop / Back to Input", icon="stop", on_click=stop_train_fetch,
                ).props("dense outline color=negative")
            ui.label(
                "Use Skip if a fetch or captcha for the CURRENT enrollment seems stuck -- "
                "it moves straight on to the next one. Use Stop to abandon the whole batch "
                "and go back to editing your sample enrollment numbers."
            ).classes("text-xs text-gray-500 mt-1")
            with ui.column().classes("gap-0 mt-2 font-mono"):
                for line in state["train_fetch_log"]:
                    ui.label(line).classes("text-xs")
        render_captcha_box(container)


def render_select_ranges(container):
    idx = state["train_current_idx"]
    label = state["train_order"][idx]
    sample_enr, chunk = state["train_samples"][label][0]

    # Fresh element refs for this semester's panel -- anything from a
    # previous semester is gone now that its DOM was torn down.
    state["train_cell_elements"] = {}
    state["train_group_icons"] = {}

    prev_label, prev_entry = _previous_ranges_entry()
    # Default to importing the previous semester's cell addresses --
    # these flat identity/summary fields (Institute/Name/Enrollment/etc.)
    # sit at the same fixed spot on every semester's page for a given
    # student, so re-selecting them semester after semester is pure
    # repeated work. Subjects/Levels/Max+Obtained are NOT included here --
    # those are trained separately per semester via the wizard, since
    # that layout genuinely can differ.
    state["train_import_checked"] = bool(prev_entry)
    if prev_entry:
        state["train_collected"] = _entry_to_collected(prev_entry)
    else:
        state["train_collected"] = {key: [] for key, _ in mt.GROUPS}

    with container:
        with ui.card().classes("w-full").style("padding: 6px 14px;"):
            with ui.row().classes("items-center gap-3 no-wrap"):
                ui.label(f"Semester {idx + 1} of {len(state['train_order'])}: {label}").classes(
                    "text-sm font-bold"
                )
                ui.label(f"(sample: {sample_enr})").classes("text-xs text-gray-500")

            relevant_warnings = [w for w in state["train_warnings"] if w.startswith(label + ":")]
            if relevant_warnings:
                with ui.element("div").classes("bg-yellow-50 border border-yellow-300 rounded p-1 mt-1"):
                    for w in relevant_warnings:
                        ui.label(w).classes("text-xs text-yellow-800")

            if prev_entry:
                with ui.row().classes("items-center gap-2 mt-1"):
                    ui.checkbox(
                        f"Import same cell addresses as {prev_label}",
                        value=True,
                        on_change=lambda e: toggle_import_previous(e.value),
                    ).classes("text-xs")
                ui.label(
                    "Imported groups are shown ticked and highlighted purple below. Click Clear "
                    "then re-select to override any single group."
                ).classes("text-xs text-gray-500")

            with ui.expansion("How to select ranges", icon="help_outline").classes("w-full text-xs mt-1"):
                ui.label(
                    'Click and drag across cells to select a range (a plain click selects just '
                    'one cell). Then click "Add" under whichever group it belongs to -- add '
                    'several selections per group if needed (e.g. Maximum Marks, where MAX/OBT '
                    'columns alternate).'
                ).classes("text-xs text-gray-500")

        with ui.row().classes("w-full gap-4 items-start no-wrap mt-4"):
            with ui.column().classes("w-72 gap-2 flex-shrink-0 overflow-y-auto").style("max-height: 80vh").props('id=trainer-sidebar-scroll'):
                with ui.card().classes("w-full"):
                    ui.label("Institute Name && Address").classes("text-sm font-semibold")
                    ui.label("(typed once, reused on every report)").classes("text-xs text-gray-400")
                    ui.input(
                        label="Institute Name", value=state["train_institute_name"],
                        on_change=lambda e: state.update(train_institute_name=e.value),
                    ).classes("w-full")
                    ui.input(
                        label="Institute Address", value=state["train_institute_address"],
                        on_change=lambda e: state.update(train_institute_address=e.value),
                    ).classes("w-full")

                for gidx, (key, glabel) in enumerate(NON_SUBJECT_GROUPS, start=1):
                    with ui.card().classes("w-full"):
                        with ui.row().classes("items-center justify-between w-full"):
                            ui.label(f"{gidx}. {glabel}").classes("text-sm font-semibold")
                            icon = ui.icon("check_circle", color="green")
                            icon.set_visibility(bool(state["train_collected"][key]))
                            state["train_group_icons"][key] = icon
                        with ui.row().classes("gap-2 w-full"):
                            ui.button("Add", on_click=lambda k=key: add_to_group(k)).props(
                                "dense outline"
                            ).classes("flex-grow")
                            ui.button("Clear", on_click=lambda k=key: clear_group(k)).props(
                                "dense outline color=grey"
                            ).classes("flex-grow")

                ui.button(
                    "Continue \u2192 Select Subjects",
                    icon="arrow_forward",
                    on_click=save_semester_ranges,
                ).classes("w-full mt-2").props("unelevated color=primary")

            with ui.column().classes("gap-1 overflow-y-auto overflow-x-hidden flex-grow").style(
                "max-height: 80vh"
            ).props('id=trainer-grid-scroll'):
                for pos, table in enumerate(chunk):
                    grid_data = mt.expand_table_grid(table)
                    grid_col = ui.column().classes("gap-0 w-full")
                    render_grid(grid_col, pos, grid_data)

    if prev_entry:
        _paint_collected_groups("bg-purple-200")


def render_train_done(container):
    with container:
        with ui.card().classes("w-full"):
            ui.label("Training complete!").classes("text-xl font-bold text-green-700")
            trained = list(state["train_mapping"].keys())
            ui.label(f"Semester(s) trained: {', '.join(trained) if trained else '(none)'}").classes(
                "text-sm mt-2"
            )
            ui.label(
                f"Saved to {mt.MAPPING_FILE} and semester headings written to {mt.DB_FILE}."
            ).classes("text-xs text-gray-500 mt-1")

            warnings = state["train_warnings"]
            if warnings:
                with ui.element("div").classes(
                    "bg-red-50 border border-red-400 rounded p-2 mt-3"
                ):
                    ui.label(
                        f"\u26a0 {len(warnings)} flag(s) found during training -- review before "
                        f"trusting extracted data:"
                    ).classes("text-sm font-bold text-red-700")
                    for w in warnings:
                        ui.label(w).classes("text-xs text-red-700 mt-1")

            with ui.row().classes("gap-2 mt-4"):
                ui.button(
                    "Train More Semesters", icon="arrow_back",
                    on_click=lambda: (state.update(train_step="input"), render_top_area(), render_mode_content()),
                ).props("outline")
                ui.button(
                    "Continue to Extract Mode \u2192", icon="arrow_forward",
                    on_click=lambda: mark_complete_and_advance("train"),
                ).props("unelevated color=primary")


# =======================================================================
# EXTRACT MODE
# =======================================================================
# Bulk version of the same fetch used in Train: for every pasted
# enrollment number, fetch its result live (captcha solved inline),
# apply the already-trained layout_mapping.json to pull out the fields,
# and save straight to the database. One enrollment failing (bad
# number, no result, captcha cancelled, unexpected page structure)
# never stops the batch -- it's logged and flagged for review, and
# extraction moves on to the next enrollment.

def _load_mapping_or_none():
    if not os.path.exists(mt.MAPPING_FILE):
        return None
    mapping = mt.load_mapping()
    return mapping or None


def _clear_extract_progress():
    state["extract_total"] = 0
    state["extract_done_list"] = []
    state["extract_pending_list"] = []
    state["extract_stop_requested"] = False


def _unique_enrollment_lines():
    """Pasted enrollment numbers, in order, duplicates removed."""
    seen, out = set(), []
    for e in enrollment_lines():
        if e not in seen:
            seen.add(e)
            out.append(e)
    return out


def _db_extracted_enrollments():
    """Every enrollment that already has saved results in the active scheme's database."""
    found = set()
    if not os.path.exists(mt.DB_FILE):
        return found
    conn = sqlite3.connect(mt.DB_FILE)
    for table in ("student_records", "subjectwise_student_records", "canonical_marks"):
        try:
            found |= {r[0] for r in conn.execute(f"SELECT DISTINCT enrollment FROM {table}") if r[0]}
        except sqlite3.OperationalError:
            pass
    conn.close()
    return found


def stop_extraction():
    """Stops the batch after the current enrollment. Anything already extracted
    is already saved, and the rest stay in the paste box for next time."""
    state["extract_stop_requested"] = True
    pending = state.get("captcha_pending")
    if pending:
        pending["result"]["value"] = ""
        pending["done"].set()
    ui.notify("Stopping -- progress so far is saved.", type="info")


def render_extract_progress():
    """Two read-only boxes: extracted vs yet-to-extract, each with count / total."""
    total = state["extract_total"]
    done = state["extract_done_list"]
    pending = state["extract_pending_list"]
    ui.linear_progress(value=(len(done) / total) if total else 0, show_value=False).classes("mt-2")
    with ui.row().classes("w-full gap-4 mt-2 flex-nowrap"):
        with ui.column().classes("flex-1 gap-0"):
            ui.label(f"Extracted: {len(done)} / {total}").classes("text-xs font-semibold text-green-700")
            ui.textarea(value="\n".join(done)).classes("w-full").props("outlined readonly rows=6 dense")
        with ui.column().classes("flex-1 gap-0"):
            ui.label(f"Yet to extract: {len(pending)} / {total}").classes("text-xs font-semibold text-orange-700")
            ui.textarea(value="\n".join(pending)).classes("w-full").props("outlined readonly rows=6 dense")


async def start_extraction():
    pasted = _unique_enrollment_lines()
    if not pasted:
        ui.notify("Paste at least one enrollment number above first.", type="warning")
        return

    mapping = _load_mapping_or_none()
    if mapping is None:
        ui.notify(
            f"Could not find {mt.MAPPING_FILE}. Finish Train mode first.",
            type="negative",
        )
        return

    # Anything already in the database is treated as extracted: counted, removed
    # from the paste box, and NOT fetched again -- this is what makes a revisit
    # continue with only the remaining enrollment numbers.
    in_db = _db_extracted_enrollments()
    already = [e for e in pasted if e in in_db]
    todo = [e for e in pasted if e not in in_db]

    state["extract_total"] = len(pasted)
    state["extract_done_list"] = list(already)
    state["extract_pending_list"] = list(todo)
    state["extract_stop_requested"] = False
    state["extract_run_id"] += 1
    run_id = state["extract_run_id"]
    state["enrollment_text"] = "\n".join(todo)
    state["extract_step"] = "running"
    state["extract_log"] = []
    state["extract_summary"] = None
    if already:
        state["extract_log"].append(f"{len(already)} enrollment(s) already extracted earlier -- skipped.")
    if not todo:
        state["extract_log"].append("Nothing left to extract.")
    render_top_area()
    render_mode_content()

    session = requests.Session()
    all_review = []
    processed = 0
    skipped = 0

    for enr in todo:
        if state["extract_run_id"] != run_id:
            return  # scheme switched / run aborted -- leave the new state alone
        if state["extract_stop_requested"]:
            _log("Stopped by user.", "extract_log")
            break
        _log(f"Fetching {enr} ...", "extract_log")
        try:
            html, attempts = await web_fetch_result_html_with_retry(
                session, enr, log_key="extract_log"
            )
            if state["extract_run_id"] != run_id:
                return  # never save into a different scheme's database
            if not html:
                if state["extract_stop_requested"]:
                    _log("Stopped by user.", "extract_log")
                    break
                _log("  Skipped (fetch/captcha cancelled).", "extract_log")
                all_review.append({
                    "enrollment": enr, "semester_label": None,
                    "reason": "Fetch/captcha failed.",
                })
                skipped += 1
                continue

            extracted, canonical_rows, subjectwise_records, review = mt.apply_mapping_to_html(
                html, mapping, enr, mt.DB_FILE
            )
            all_review.extend(review)
            # Saved immediately, one enrollment at a time, so an interrupted run
            # never loses what was already extracted.
            mt.save_records_to_db(extracted, review, mt.DB_FILE)

            if not (extracted or canonical_rows or subjectwise_records):
                _log(
                    f"  Nothing extracted after {attempts} attempt(s) (wrong enrollment number, "
                    f"no result available, or repeated wrong captcha). Kept in the list.",
                    "extract_log",
                )
                skipped += 1
                continue

            mt.save_canonical_marks_to_db(canonical_rows, mt.DB_FILE)
            mt.save_subjectwise_student_records_to_db(subjectwise_records, mt.DB_FILE)
            if attempts > 1:
                _log(
                    f"  Resolved after {attempts} attempt(s) "
                    f"(earlier attempt(s) likely had a wrong captcha).",
                    "extract_log",
                )
            processed += 1
            state["extract_done_list"].append(enr)
            if enr in state["extract_pending_list"]:
                state["extract_pending_list"].remove(enr)
            state["enrollment_text"] = "\n".join(state["extract_pending_list"])
            render_top_area()
            _log(
                f"  {len(extracted)} field(s) + {len(subjectwise_records)} subject-wise mark(s) "
                f"extracted, {len(review)} flagged for review.",
                "extract_log",
            )
        except Exception as e:
            # One enrollment blowing up must never kill the rest of the batch.
            _log(f"  ERROR processing {enr}: {e}. Skipping and continuing.", "extract_log")
            all_review.append({
                "enrollment": enr, "semester_label": None,
                "reason": f"Unhandled error during extraction: {e}",
            })
            skipped += 1

    if state["extract_run_id"] != run_id:
        return
    if processed:
        invalidate_downstream_data()

    state["extract_summary"] = {
        "total": len(pasted),
        "already": len(already),
        "processed": processed,
        "skipped": skipped,
        "remaining": len(state["extract_pending_list"]),
        "review": len(all_review),
    }
    state["extract_review_details"] = all_review
    state["extract_step"] = "done"
    render_mode_content()


def invalidate_report_and_coursecode_caches():
    """Lighter-weight cousin of invalidate_downstream_data(), used when a
    single enrollment's data changes mid-run inside the Recheck Manual/
    Delete queue -- clears the Course Codes/Report/Yearly-gap caches (so
    they recalculate against the new data) WITHOUT touching the queue's
    own progress state (recheck_queue_mode/list/pos/stats/log), which
    invalidate_downstream_data() would otherwise reset on every single
    save."""
    state["coursecode_data"] = None
    state["coursecode_values"] = {}
    state["coursecode_faculty_values"] = {}
    state["coursecode_faculty_touched"] = set()
    state["coursecode_autofill"] = False
    state["coursecode_autofilled_keys"] = set()

    state["report_step"] = "select"
    state["report_log"] = []
    state["report_generated_files"] = []

    state["yearly_gaps"] = []
    state["yearly_gap_upload_path"] = None
    state["yearly_gap_upload_name"] = None
    state["yearly_gap_matches"] = []

    state["completed"].discard("coursecodes")
    state["completed"].discard("report")


def invalidate_downstream_data():
    """Called whenever the underlying extracted student data changes --
    a new extraction batch is saved, the enrollment list is swapped out
    for a fresh one, or the database is erased -- so every later mode
    recalculates from what's actually in the database now instead of
    showing stale cached results from before the change. Train mode's
    semester/field mapping describes page *layout*, not student data,
    so it's deliberately left untouched here."""
    invalidate_report_and_coursecode_caches()

    state["recheck_step"] = "choose"
    state["recheck_log"] = []
    state["recheck_summary"] = None
    state["recheck_queue_mode"] = None
    state["recheck_queue_list"] = []
    state["recheck_queue_pos"] = 0
    state["recheck_queue_stats"] = {}
    state["recheck_queue_log"] = []
    state["recheck_manual_enrollment"] = ""
    state["recheck_manual_records"] = None
    state["recheck_manual_semesters"] = []
    state["recheck_manual_subject_names"] = {}
    state["recheck_manual_components"] = {}
    state["recheck_manual_values"] = {}
    state["recheck_manual_originals"] = {}
    state["recheck_manual_delete_semesters"] = set()
    state["recheck_delete_semesters_present"] = []
    state["recheck_manual_subjectwise_values"] = {}
    state["recheck_manual_subjectwise_originals"] = {}
    state["recheck_manual_subjectwise_meta"] = {}

    # Force Course Codes / Report / Recheck to be re-confirmed against
    # the new data -- re-locks them in the sidebar until the user goes
    # through each one again.
    state["completed"].discard("recheck")


def reset_extraction():
    state["extract_step"] = "idle"
    state["extract_log"] = []
    state["extract_summary"] = None
    state["extract_review_details"] = []
    _clear_extract_progress()
    render_mode_content()


def load_new_database():
    """'Load New Database' button -- clears the shared enrollment paste
    box so the user can type in a completely fresh list, without
    touching whatever's already saved in the database itself."""
    state["enrollment_text"] = ""
    state["extract_step"] = "idle"
    state["extract_log"] = []
    state["extract_summary"] = None
    _clear_extract_progress()
    invalidate_downstream_data()
    render_top_area()
    render_mode_content()


def confirm_erase_database():
    """'Erase Database' button -- destructive, so confirm first."""
    with ui.dialog() as dialog, ui.card():
        ui.label("Erase all extracted student data?").classes("text-lg font-semibold")
        ui.label(
            "This wipes every enrollment's extracted marks/results out of the database "
            "completely. Trained ranges, course codes, and report settings are kept. "
            "This cannot be undone."
        ).classes("text-sm text-gray-600 mt-1")
        with ui.row().classes("gap-2 mt-4 justify-end"):
            ui.button("Cancel", on_click=dialog.close).props("outline")
            ui.button(
                "Erase Everything", icon="delete_forever", color="negative",
                on_click=lambda: (dialog.close(), erase_database_confirmed()),
            )
    dialog.open()


def erase_database_confirmed():
    n = mt.erase_extracted_data(mt.DB_FILE)
    invalidate_downstream_data()
    state["extract_step"] = "idle"
    state["extract_log"] = []
    state["extract_summary"] = None
    _clear_extract_progress()
    ui.notify(f"Erased {n} enrollment(s) from the database.", type="positive")
    render_mode_content()


def render_extract_idle(container):
    with container:
        with ui.card().classes("w-full"):
            ui.label("Extract").classes("text-xl font-bold")
            ui.label(MODE_DESCRIPTIONS["extract"]).classes("text-sm text-gray-600")
            ui.separator()
            mapping = _load_mapping_or_none()
            if mapping is None:
                ui.label(
                    f"No {mt.MAPPING_FILE} found -- finish Train mode first."
                ).classes("text-sm text-red-600 mt-3")
            else:
                trained = ", ".join(mapping.keys())
                ui.label(f"Trained semester(s): {trained}").classes("text-xs text-gray-500 mt-3")

            existing = mt.load_extracted_enrollments(mt.DB_FILE)
            ui.label(f"Already extracted in the database ({len(existing)}):").classes(
                "text-sm font-semibold mt-3"
            )
            ui.textarea(
                value="\n".join(existing) if existing else "(none yet)",
            ).classes("w-full").props("outlined readonly rows=5 dense")

            with ui.row().classes("gap-2 mt-2"):
                ui.button(
                    "Erase Database", icon="delete_forever", on_click=confirm_erase_database,
                ).props("outline color=negative")
                ui.button(
                    "Load New Database", icon="refresh", on_click=load_new_database,
                ).props("outline")

            n = len(enrollment_lines())
            ui.label(f"{n} enrollment number(s) currently pasted above.").classes(
                "text-sm mt-2"
            )
            _pasted = _unique_enrollment_lines()
            if _pasted:
                _in_db = _db_extracted_enrollments()
                _already = sum(1 for e in _pasted if e in _in_db)
                ui.label(
                    f"{_already} of {len(_pasted)} are already extracted (they'll be removed from the "
                    f"box, not fetched again); {len(_pasted) - _already} remaining."
                ).classes("text-xs text-gray-500")
            ui.button(
                "Start Extraction", icon="cloud_download", on_click=start_extraction,
            ).classes("mt-3").props("unelevated color=primary").set_enabled(
                n > 0 and mapping is not None
            )


def render_extract_running(container):
    with container:
        with ui.card().classes("w-full"):
            ui.label("Extracting...").classes("text-lg font-semibold")
            ui.label("Solve each captcha as it appears below.").classes("text-xs text-gray-500")
            ui.button("Stop", icon="stop", on_click=stop_extraction).props(
                "dense outline color=negative"
            ).classes("mt-1")
            render_extract_progress()
            with ui.column().classes("gap-0 mt-2 font-mono"):
                for line in state["extract_log"]:
                    ui.label(line).classes("text-xs")
        render_captcha_box(container)


def render_extract_done(container):
    summary = state["extract_summary"] or {}
    with container:
        with ui.card().classes("w-full"):
            ui.label("Extraction complete!").classes("text-xl font-bold text-green-700")
            with ui.grid(columns=2).classes("gap-x-6 gap-y-1 mt-3 text-sm"):
                ui.label("Enrollment numbers submitted:")
                ui.label(str(summary.get("total", 0))).classes("font-semibold")
                ui.label("Already extracted earlier (skipped):")
                ui.label(str(summary.get("already", 0))).classes("font-semibold")
                ui.label("Successfully processed:")
                ui.label(str(summary.get("processed", 0))).classes("font-semibold")
                ui.label("Skipped / failed:")
                ui.label(str(summary.get("skipped", 0))).classes("font-semibold")
                ui.label("Still to extract (left in the box):")
                ui.label(str(summary.get("remaining", 0))).classes(
                    "font-semibold" + (" text-orange-600" if summary.get("remaining") else "")
                )
                ui.label("Flagged for review:")
                ui.label(str(summary.get("review", 0))).classes(
                    "font-semibold" + (" text-orange-600" if summary.get("review") else "")
                )
            render_extract_progress()

            review_details = state.get("extract_review_details") or []
            if review_details:
                with ui.element("div").classes(
                    "bg-red-50 border border-red-400 rounded p-2 mt-3"
                ):
                    ui.label(f"\u26a0 {len(review_details)} item(s) flagged -- reason(s):").classes(
                        "text-sm font-bold text-red-700"
                    )
                    for item in review_details:
                        enr = item.get("enrollment", "?")
                        sem = item.get("semester_label") or "(no semester detected)"
                        reason = item.get("reason", "")
                        ui.label(f"{enr} -- {sem}: {reason}").classes("text-xs text-red-700 mt-1")

            ui.label(f"Saved to {mt.DB_FILE}.").classes("text-xs text-gray-500 mt-2")
            with ui.row().classes("gap-2 mt-4"):
                ui.button(
                    "Extract More", icon="replay", on_click=reset_extraction,
                ).props("outline")
                ui.button(
                    "Continue to Course Codes Mode \u2192", icon="arrow_forward",
                    on_click=lambda: mark_complete_and_advance("extract"),
                ).props("unelevated color=primary")


# =======================================================================
# COURSE CODES MODE
# =======================================================================
# One-time (but freely re-editable) data entry: Abbreviation / Course
# Code per subject, plus one Faculty field per Level 1 template node that
# actually applies to that subject (per the Tree Checkboxes step -- a
# Practical-only subject just doesn't get a THEORY-faculty box). Subjects
# and their applicable components come from the subject-wise trainer
# (subjects + component_template + subject_node_disabled) -- no fetching
# or captchas here, purely manual entry against the database.
#
# Faculty is usually the same person for every Level 1 node of one
# subject, so typing it into the FIRST node's box auto-fills the rest --
# individually editing any one of them exempts it from that auto-fill
# from then on (tracked in coursecode_faculty_touched).

def load_coursecode_data(force=False):
    """(Re)loads subjects/components/prefill values from the database
    into state. Cheap enough to call every time Course Codes mode is
    entered; `force=True` discards any in-progress unsaved edits and
    reloads from whatever's currently saved in the DB."""
    if state["coursecode_data"] is not None and not force:
        return

    subj_components = mt.get_subjects_with_level1_components(mt.DB_FILE)
    existing_codes = mt.load_subject_course_codes_v2(mt.DB_FILE)
    existing_faculty = mt.load_subject_component_faculty_v2(mt.DB_FILE)

    values = {}
    faculty_values = {}
    touched = set()
    for sem, subj_list in subj_components:
        for subject_index, _name, nodes in subj_list:
            prior = existing_codes.get((sem, subject_index), {})
            values[(sem, subject_index)] = {
                "abbreviation": prior.get("abbreviation") or "",
                "course_code": prior.get("course_code") or "",
            }
            node_vals = []
            for node_id, _label in nodes:
                fv = existing_faculty.get((sem, subject_index, node_id)) or ""
                faculty_values[(sem, subject_index, node_id)] = fv
                node_vals.append(fv)
            # if this subject's saved faculty already differs across its
            # nodes, preserve that instead of collapsing it on next edit
            distinct_nonblank = {v.strip() for v in node_vals if v.strip()}
            if len(distinct_nonblank) > 1:
                for node_id, _label in nodes:
                    touched.add((sem, subject_index, node_id))

    state["coursecode_data"] = subj_components
    state["coursecode_values"] = values
    state["coursecode_faculty_values"] = faculty_values
    state["coursecode_faculty_touched"] = touched
    state["coursecode_autofill"] = False
    state["coursecode_autofilled_keys"] = set()


def reload_coursecode_data():
    load_coursecode_data(force=True)
    render_mode_content()
    ui.notify("Reloaded from database -- any unsaved edits were discarded.", type="info")


def on_coursecode_faculty_input(value, sem, subject_index, node_id):
    """Fires on every keystroke -- just stores the value, no re-render, so
    typing a full name behaves exactly like Abbreviation/Course Code."""
    state["coursecode_autofilled_keys"].discard((sem, subject_index, node_id))
    state["coursecode_faculty_values"][(sem, subject_index, node_id)] = value


def on_coursecode_faculty_blur(sem, subject_index, node_id, sibling_node_ids):
    """Fires once, when the box loses focus (name fully typed) -- THIS is
    where it propagates to untouched sibling boxes and re-renders, so the
    person never gets kicked out mid-keystroke."""
    key = (sem, subject_index, node_id)
    value = state["coursecode_faculty_values"].get(key, "")
    state["coursecode_faculty_touched"].add(key)

    propagated = False
    for other_id in sibling_node_ids:
        if other_id == node_id:
            continue
        other_key = (sem, subject_index, other_id)
        if other_key not in state["coursecode_faculty_touched"]:
            if state["coursecode_faculty_values"].get(other_key, "") != value:
                state["coursecode_faculty_values"][other_key] = value
                propagated = True
    if propagated:
        render_mode_content()  # refresh sibling boxes to show the propagated value


def _random_coursecode_value():
    """Random combination of letters and digits, e.g. 'XJ482'."""
    letters = "".join(random.choices(string.ascii_uppercase, k=2))
    digits = "".join(random.choices(string.digits, k=3))
    return letters + digits


def on_coursecode_autofill_toggle(e):
    """Checkbox handler: when checked, fill every currently-empty box with a
    random text+number value and remember which boxes were touched so they
    can be cleared again on uncheck. Boxes the user already filled in
    (manually, or before checking this box) are left alone either way."""
    state["coursecode_autofill"] = e.value
    data = state["coursecode_data"] or []

    if e.value:
        for sem, subj_list in data:
            for subject_index, _subject_name, nodes in subj_list:
                vals = state["coursecode_values"].setdefault((sem, subject_index), {})

                if not (vals.get("abbreviation") or "").strip():
                    vals["abbreviation"] = _random_coursecode_value()
                    state["coursecode_autofilled_keys"].add((sem, subject_index, "abbreviation"))

                if not (vals.get("course_code") or "").strip():
                    vals["course_code"] = _random_coursecode_value()
                    state["coursecode_autofilled_keys"].add((sem, subject_index, "course_code"))

                for node_id, _label in nodes:
                    key = (sem, subject_index, node_id)
                    fval = state["coursecode_faculty_values"].get(key, "")
                    if not (fval or "").strip():
                        state["coursecode_faculty_values"][key] = _random_coursecode_value()
                        state["coursecode_autofilled_keys"].add(key)
    else:
        # Only clear boxes that WE filled in -- never touch anything the
        # user typed themselves.
        for key in state["coursecode_autofilled_keys"]:
            sem, subject_index, field = key
            if field in ("abbreviation", "course_code"):
                vals = state["coursecode_values"].get((sem, subject_index))
                if vals is not None:
                    vals[field] = ""
            else:
                node_id = field
                state["coursecode_faculty_values"][(sem, subject_index, node_id)] = ""
        state["coursecode_autofilled_keys"] = set()

    render_mode_content()


def save_coursecodes(advance=False):
    data = state["coursecode_data"] or []
    code_entries = []
    faculty_entries = []
    subject_count = 0

    for sem, subj_list in data:
        for subject_index, subject_name, nodes in subj_list:
            subject_count += 1
            vals = state["coursecode_values"].get((sem, subject_index), {})
            code_entries.append({
                "semester_label": sem, "subject_index": subject_index, "subject_name": subject_name,
                "abbreviation": (vals.get("abbreviation") or "").strip(),
                "course_code": (vals.get("course_code") or "").strip(),
            })
            for node_id, label in nodes:
                fv = (state["coursecode_faculty_values"].get((sem, subject_index, node_id)) or "").strip()
                faculty_entries.append({
                    "semester_label": sem, "subject_index": subject_index,
                    "node_id": node_id, "component_label": label, "faculty_name": fv,
                })

    mt.save_subject_course_codes_v2_to_db(code_entries, mt.DB_FILE)
    mt.save_subject_component_faculty_v2_to_db(faculty_entries, mt.DB_FILE)
    ui.notify(f"Saved course codes for {subject_count} subject(s).", type="positive")

    if advance:
        # Report is not part of the MODE_ORDER chain (it's global) --
        # still record "coursecodes" complete, then jump straight to
        # Report instead of mark_complete_and_advance's index-based
        # hand-off.
        state["completed"].add("coursecodes")
        update_mode_buttons()
        select_mode("report")


def render_coursecodes(container):
    load_coursecode_data()
    data = state["coursecode_data"]

    with container:
        with ui.card().classes("w-full"):
            with ui.row().classes("items-center justify-between w-full"):
                ui.label("Course Codes").classes("text-xl font-bold")
                ui.button(
                    "Reload from Database", icon="refresh", on_click=reload_coursecode_data,
                ).props("outline dense")
            ui.label(MODE_DESCRIPTIONS["coursecodes"]).classes("text-sm text-gray-600")
            ui.label(
                "Faculty is usually the same for every component of one subject -- type it once "
                "and it fills the rest; edit any single box to override just that one."
            ).classes("text-xs text-gray-500 mt-1")

            ui.checkbox(
                "Auto-fill empty boxes with random values",
                value=state["coursecode_autofill"],
                on_change=on_coursecode_autofill_toggle,
            ).classes("mt-2").props("dense")

            if not data:
                ui.separator()
                ui.label(
                    "No subjects found -- finish the subject-wise trainer (Steps 1-5) for at "
                    "least one semester in Train mode first."
                ).classes("text-sm text-red-600 mt-3")
                return

        for sem, subj_list in data:
            with ui.card().classes("w-full mt-3"):
                ui.label(sem.title()).classes("text-md font-bold text-blue-700")
                sem_components = []
                for _idx, _name, nodes in subj_list:
                    for _node_id, label in nodes:
                        if label not in sem_components:
                            sem_components.append(label)

                with ui.element("div").classes("overflow-x-auto w-full"):
                    with ui.column().classes("gap-1 mt-2").style("min-width: max-content;"):
                        with ui.row().classes("gap-1 flex-nowrap items-center"):
                            ui.label("Subject").classes("text-xs font-semibold w-56 flex-shrink-0")
                            ui.label("Abbreviation").classes("text-xs font-semibold w-28 flex-shrink-0")
                            ui.label("Course Code").classes("text-xs font-semibold w-28 flex-shrink-0")
                            for c in sem_components:
                                ui.label(f"{c.title()} Faculty").classes(
                                    "text-xs font-semibold w-36 flex-shrink-0"
                                )

                        for subject_index, subject_name, nodes in subj_list:
                            vals = state["coursecode_values"].get((sem, subject_index), {})
                            node_by_label = {label: node_id for node_id, label in nodes}
                            sibling_ids = [node_id for node_id, _label in nodes]

                            with ui.row().classes("gap-1 flex-nowrap items-center"):
                                ui.label(subject_name).classes("text-xs w-56 flex-shrink-0")

                                def on_abbrev(e, s=sem, i=subject_index):
                                    state["coursecode_values"].setdefault((s, i), {})["abbreviation"] = e.value
                                    state["coursecode_autofilled_keys"].discard((s, i, "abbreviation"))

                                def on_code(e, s=sem, i=subject_index):
                                    state["coursecode_values"].setdefault((s, i), {})["course_code"] = e.value
                                    state["coursecode_autofilled_keys"].discard((s, i, "course_code"))

                                ui.input(
                                    value=vals.get("abbreviation", ""), on_change=on_abbrev,
                                ).classes("w-28 flex-shrink-0").props("dense outlined")
                                ui.input(
                                    value=vals.get("course_code", ""), on_change=on_code,
                                ).classes("w-28 flex-shrink-0").props("dense outlined")

                                for c in sem_components:
                                    node_id = node_by_label.get(c)
                                    if node_id is not None:
                                        fval = state["coursecode_faculty_values"].get((sem, subject_index, node_id), "")
                                        fac_input = ui.input(
                                            value=fval,
                                            on_change=lambda e, s=sem, i=subject_index, n=node_id:
                                                on_coursecode_faculty_input(e.value, s, i, n),
                                        ).classes("w-36 flex-shrink-0").props("dense outlined")
                                        fac_input.on(
                                            "blur",
                                            lambda e, s=sem, i=subject_index, n=node_id, sib=sibling_ids:
                                                on_coursecode_faculty_blur(s, i, n, sib),
                                        )
                                    else:
                                        ui.input(value="N/A").classes(
                                            "w-36 flex-shrink-0 opacity-50"
                                        ).props("dense outlined disable")

        with ui.card().classes("w-full mt-3"):
            with ui.row().classes("gap-2"):
                ui.button(
                    "Save", icon="save", on_click=lambda: save_coursecodes(advance=False),
                ).props("outline color=primary")
                ui.button(
                    "Save && Continue to Report Mode \u2192", icon="arrow_forward",
                    on_click=lambda: save_coursecodes(advance=True),
                ).props("unelevated color=primary")


# =======================================================================
# REPORT MODE
# =======================================================================
# Build PDF reports straight from the database -- no fetching, no
# captchas, no Excel. Mirrors ask_report_selection()/run_report_mode():
# 7 report types, each independently toggle-able with its own Regular/
# EX/Both status filter (K7 Part B additionally needs a fail-% highlight
# threshold and requires Course Codes to be filled in; Bright/Weak needs
# weak/bright percentage thresholds). Each generate_*_pdf() call is left
# to build its own default filename (so naming stays in exactly one
# place) -- the file is then moved into REPORTS_DIR for serving.

def _generate_and_collect(label, fn, *args, **kwargs):
    """Calls one of msbte_tool's generate_*_pdf functions (which saves
    into the current working directory using its own default filename
    and returns that filename), then moves the result into REPORTS_DIR
    so every report of this run lives in one place to serve/download.

    Returns None if the function itself returned None -- which happens
    whenever there's simply no data for that particular report (e.g. a
    semester nothing was extracted for yet, or no enrollments match the
    chosen Regular/EX/Both filter). That's not an error -- the caller
    logs it and moves on to the next report instead of stopping the
    whole batch.
    """
    produced_path = fn(*args, **kwargs)
    if produced_path is None:
        return None
    os.makedirs(REPORTS_DIR, exist_ok=True)
    dest = os.path.join(REPORTS_DIR, os.path.basename(produced_path))
    if os.path.abspath(produced_path) != os.path.abspath(dest):
        shutil.move(produced_path, dest)
    return label, dest


def _report_log(line):
    state["report_log"].append(line)
    render_mode_content()


def run_yearly_gap_check():
    """Manual-only (Check button) -- computes fresh, saves the result as
    the current 'group' of flagged gaps in the database, and re-renders.
    This is the only thing that unblocks Yearly_Result_Report /
    Yearly_Eligible_NonEligible_Report."""
    gaps = mt.compute_yearly_semester_gaps(mt.DB_FILE)
    mt.save_yearly_gap_flags_to_db(gaps, mt.DB_FILE)
    state["yearly_gaps"] = gaps
    if gaps:
        ui.notify(
            f"Found {len(gaps)} missing-semester gap(s). Upload a secondary database below to fill them.",
            type="warning",
        )
    else:
        ui.notify("No missing-semester gaps found. Yearly reports are unblocked.", type="positive")
    render_mode_content()


def download_yearly_gap_pdf():
    path = mt.generate_yearly_gap_report_pdf(mt.DB_FILE)
    if path is None:
        ui.notify("No gaps on record -- run the Gap Check first.", type="warning")
        return
    os.makedirs(REPORTS_DIR, exist_ok=True)
    dest = os.path.join(REPORTS_DIR, os.path.basename(path))
    if os.path.abspath(path) != os.path.abspath(dest):
        shutil.move(path, dest)
    ui.download(dest, os.path.basename(dest))


async def on_yearly_gap_db_upload(e):
    """Saves the uploaded secondary database file and runs a READ-ONLY
    match check against the current gaps -- does NOT write anything to
    the real database yet. The result (found/not-found per gap) is
    shown in render_yearly_gap_check(); apply_yearly_gap_update() is
    the separate, explicit step that actually copies the data in."""
    os.makedirs(GAP_UPLOAD_DIR, exist_ok=True)
    upload_name = e.file.name
    upload_path = os.path.join(GAP_UPLOAD_DIR, upload_name)
    with open(upload_path, "wb") as f:
        f.write(await e.file.read())

    try:
        matches = mt.check_yearly_gap_matches(upload_path, mt.DB_FILE)
    except Exception as ex:
        ui.notify(f"Could not read that file as a database: {ex}", type="negative")
        return

    state["yearly_gap_upload_path"] = upload_path
    state["yearly_gap_upload_name"] = upload_name
    state["yearly_gap_matches"] = matches

    found_n = sum(1 for m in matches if m["found"])
    not_found_n = len(matches) - found_n
    if not matches:
        ui.notify("No missing-semester gaps right now -- nothing to check against.", type="positive")
    elif found_n and not not_found_n:
        ui.notify(
            f"Match found for all {found_n} gap(s) in {upload_name}. Review below, then click "
            "Update Database.",
            type="positive",
        )
    elif found_n:
        ui.notify(
            f"{found_n} of {len(matches)} gap(s) matched in {upload_name}; {not_found_n} not found. "
            "Review below, then click Update Database.",
            type="warning",
        )
    else:
        ui.notify(f"None of the {len(matches)} gap(s) were found in {upload_name}.", type="negative")
    render_mode_content()


def apply_yearly_gap_update():
    """'Update Database' button -- actually copies in whatever the last
    match check found, using the same uploaded file. Separate, explicit
    step from the upload itself, so nothing is written until this is
    clicked."""
    upload_path = state.get("yearly_gap_upload_path")
    if not upload_path or not os.path.exists(upload_path):
        ui.notify("Upload a secondary database first.", type="warning")
        return

    result = mt.fill_yearly_gaps_from_secondary_db(upload_path, mt.DB_FILE)
    filled_n = len(result["filled"])
    missing_n = len(result["still_missing"])

    gaps = mt.compute_yearly_semester_gaps(mt.DB_FILE)
    mt.save_yearly_gap_flags_to_db(gaps, mt.DB_FILE)
    state["yearly_gaps"] = gaps
    # Clear the match-check display -- it's about to be stale either way
    # (gaps just changed), and re-uploading is cheap if more are needed.
    state["yearly_gap_upload_path"] = None
    state["yearly_gap_upload_name"] = None
    state["yearly_gap_matches"] = []

    if filled_n:
        ui.notify(f"Database updated -- filled {filled_n} gap(s).", type="positive")
    if missing_n:
        ui.notify(f"{missing_n} gap(s) still not found -- still blocked.", type="warning")
    if not gaps:
        ui.notify("All gaps resolved -- Yearly reports are unblocked.", type="positive")
    render_mode_content()


def render_yearly_gap_check():
    """Compact, collapsible block embedded inside the combined Yearly
    Result Report / Yearly Eligible-Non-Eligible List tile (see
    render_yearly_combined_tile()). Flow: Check -> (upload -> match-check
    preview) -> Update Database. See run_yearly_gap_check(),
    on_yearly_gap_db_upload(), apply_yearly_gap_update()."""
    blocked, status = mt.yearly_reports_are_blocked(mt.DB_FILE)
    gaps = state.get("yearly_gaps", [])

    if status == "not_checked":
        status_icon, status_color = "info", "grey"
    elif not gaps:
        status_icon, status_color = "check_circle", "positive"
    else:
        status_icon, status_color = "warning", "negative"

    gap_summary = (
        "not checked yet" if status == "not_checked"
        else "clean" if not gaps
        else f"{len(gaps)} gap(s) found"
    )
    with ui.expansion(
        f"Yearly Report Gap Check \u2014 {gap_summary}",
        icon=status_icon, value=bool(gaps),
    ).classes("w-full text-sm border rounded") as exp:
        exp.props(f"expand-icon-class=text-{status_color}")
        ui.label(
            "Checks every enrollment for an academic year (First/Second/Final) where only "
            "ONE of its two semesters has data in this database -- e.g. Second Semester "
            "marks exist but First Semester marks were never extracted for that enrollment. "
            "Yearly Result Report and Yearly Eligible/Non-Eligible List are blocked until "
            "this comes back clean."
        ).classes("text-xs text-gray-600")

        ui.button(
            "Check for Missing Semesters", icon="fact_check", on_click=run_yearly_gap_check,
        ).props("outline").classes("mt-2")

        if status == "not_checked":
            with ui.row().classes("items-center gap-2 mt-2"):
                ui.icon("info", color="grey")
                ui.label("Not checked yet -- click Check above.").classes("text-sm text-gray-600")
        elif not gaps:
            with ui.row().classes("items-center gap-2 mt-2"):
                ui.icon("check_circle", color="positive")
                ui.label("No missing-semester gaps found.").classes("text-sm text-green-700")
        else:
            with ui.row().classes("items-center gap-2 mt-2"):
                ui.icon("warning", color="negative")
                ui.label(f"{len(gaps)} missing-semester gap(s) found.").classes("text-sm text-red-600")

            with ui.column().classes("gap-0 mt-2 max-h-48 overflow-auto border rounded p-2 font-mono"):
                ui.label(f"{'Sr.No.':<8}{'Enrollment No.':<22}Semester").classes("text-xs font-bold")
                for i, g in enumerate(gaps, start=1):
                    ui.label(
                        f"{str(i) + '.':<8}{g['enrollment']:<22}{g['missing_semester'].title()}"
                    ).classes("text-xs")

            ui.button(
                "Download Gap List (PDF)", icon="picture_as_pdf", on_click=download_yearly_gap_pdf,
            ).props("dense outline").classes("mt-2")

            ui.label(
                "Upload a separate database file (.db) that has these enrollments' missing "
                "semester data. This only CHECKS for a match first -- nothing is written "
                "until you click Update Database below."
            ).classes("text-xs text-gray-600 mt-3")
            ui.upload(
                on_upload=on_yearly_gap_db_upload, auto_upload=True, max_files=1,
            ).props('accept=".db"').classes("mt-1")

            matches = state.get("yearly_gap_matches", [])
            upload_name = state.get("yearly_gap_upload_name")
            if upload_name and matches:
                found_n = sum(1 for m in matches if m["found"])
                ui.label(
                    f"Match check against {upload_name}: {found_n} of {len(matches)} found."
                ).classes("text-xs font-semibold mt-3")
                with ui.column().classes("gap-0 mt-1 max-h-48 overflow-auto border rounded p-2 font-mono"):
                    ui.label(f"{'':<4}{'Enrollment No.':<20}{'Semester':<18}Match").classes(
                        "text-xs font-bold"
                    )
                    for m in matches:
                        mark = "\u2713 Found" if m["found"] else "\u2717 Not found"
                        ui.label(
                            f"{'':<4}{m['enrollment']:<20}{m['missing_semester'].title():<18}{mark}"
                        ).classes("text-xs" + (" text-green-700" if m["found"] else " text-red-600"))

                ui.button(
                    "Update Database", icon="save", on_click=apply_yearly_gap_update,
                ).props("unelevated color=primary").classes("mt-2").set_enabled(found_n > 0)


def generate_reports():
    if not os.path.exists(mt.DB_FILE):
        ui.notify(f"Could not find {mt.DB_FILE}. Run Extract mode at least once first.", type="negative")
        return

    all_extracted, _all_review = mt.load_all_records_from_db(mt.DB_FILE)
    student_records = [r for r in all_extracted if r["enrollment"] is not None]
    if not student_records:
        ui.notify(f"{mt.DB_FILE} has no student data yet. Run Extract mode at least once first.", type="negative")
        return

    sel = state["report_selection"]
    if not any(sel[k]["enabled"] for k in REPORT_ORDER):
        ui.notify("Select at least one report to generate.", type="warning")
        return

    if sel["k7_partb"]["enabled"] and not mt.course_codes_are_filled(mt.DB_FILE):
        ui.notify(
            "K7 (Part B) is ticked, but no Abbreviation/Course Code has been entered yet. "
            "Fill in Course Codes mode first, or untick K7 (Part B).",
            type="negative",
        )
        return

    if sel["departmental"]["enabled"]:
        _dept_blockers = mt.dept_report_blockers(mt.DB_FILE)
        if _dept_blockers:
            ui.notify(
                "Departmental Report is blocked -- " + " | ".join(_dept_blockers)
                + " (finish the setup tables inside the Departmental Report panel).",
                type="negative", multi_line=True,
            )
            return

    simple_yearly_mode = state["yearly_report_mode"] == "simple"
    if not simple_yearly_mode:
        yearly_blocked, yearly_status = mt.yearly_reports_are_blocked(mt.DB_FILE)
        if yearly_blocked and (sel["yearly_result"]["enabled"] or sel["yearly_eligibility"]["enabled"]):
            ui.notify(
                "Yearly Result Report / Yearly Eligible list are blocked -- " + (
                    "run the Yearly Report Gap Check above first."
                    if yearly_status == "not_checked" else
                    "missing-semester gaps are on record. Upload a secondary database above to "
                    "fill them, or untick those two reports."
                ),
                type="negative",
            )
            return

    _needs = [
        REPORT_LABELS[k] for k in REPORT_ORDER
        if sel[k]["enabled"] and not (k == "yearly_eligibility" and simple_yearly_mode) and not sel[k]["statuses"]
    ]
    if _needs:
        ui.notify("Choose a category for: " + ", ".join(_needs), type="warning")
        return

    semesters_in_db = sorted(
        {r["semester_label"] for r in student_records},
        key=lambda s: mt.SEMESTER_NAMES.index(s) if s in mt.SEMESTER_NAMES else 999,
    )

    state["report_step"] = "generating"
    state["report_log"] = []
    state["report_generated_files"] = []
    render_mode_content()

    generated = []

    def _collect(label, result):
        if result is None:
            _report_log(f"  Skipped -- no data for {label}.")
        else:
            generated.append(result)

    def _run(key, title, fn, *args, **kwargs):
        """Builds `title` once per ticked category (or once for All combined)."""
        for st in sel[key]["statuses"]:
            label = f"{title} [{'All combined' if st == 'both' else st}]"
            _report_log(f"Building {label}...")
            _collect(label, _generate_and_collect(label, fn, *args, student_status=st, **kwargs))

    try:
        if sel["semester"]["enabled"]:
            for sem_label in semesters_in_db:
                _run("semester", f"{sem_label.title()} Report", mt.generate_semester_pdf, sem_label, mt.DB_FILE)

        if sel["yearly_result"]["enabled"]:
            _run("yearly_result", "Yearly Result Report", mt.generate_yearly_result_pdf, mt.DB_FILE,
                 include_yearly_block=not simple_yearly_mode)

        if sel["k7_partb"]["enabled"]:
            _run("k7_partb", "K7 (Part B) Report", mt.generate_k7_partb_pdf, mt.DB_FILE,
                 semesters=semesters_in_db, fail_pct_threshold=sel["k7_partb"]["fail_threshold"])

        if sel["k7_partc"]["enabled"]:
            _run("k7_partc", "K7 (Part C) Report", mt.generate_k7_partc_pdf, mt.DB_FILE,
                 semesters=semesters_in_db)

        if sel["yearly_eligibility"]["enabled"] and not simple_yearly_mode:
            _run("yearly_eligibility", "Yearly Eligible/Non-Eligible List",
                 mt.generate_yearly_eligibility_pdf, mt.DB_FILE)

        if sel["topper_list"]["enabled"]:
            _run("topper_list", "Semesterwise and Yearly Topper List", mt.generate_topper_list_pdf, mt.DB_FILE)

        if sel["bright_weak"]["enabled"]:
            _run("bright_weak", "Semester wise Bright/Weak Student List", mt.generate_bright_weak_pdf, mt.DB_FILE,
                 weak_threshold=sel["bright_weak"]["weak_threshold"],
                 bright_threshold=sel["bright_weak"]["bright_threshold"])

        if sel["departmental"]["enabled"]:
            _run("departmental", "Departmental Report", mt.generate_departmental_pdf, mt.DB_FILE,
                 department_name=state["logged_in"]["department_name"],
                 show_percentage=sel["departmental"].get("show_pct", False))
    except Exception as e:
        _report_log(f"ERROR: {e}")
        ui.notify(f"Report generation failed: {e}", type="negative")
        state["report_step"] = "select"
        render_mode_content()
        return

    state["report_generated_files"] = generated
    state["report_step"] = "done"
    render_mode_content()


def reset_reports():
    state["report_step"] = "select"
    state["report_log"] = []
    state["report_generated_files"] = []
    render_mode_content()


def get_semesters_in_db():
    """Every semester_label with at least one enrollment on record --
    same set generate_reports() hands to each PDF generator's
    `semesters=` argument."""
    if not os.path.exists(mt.DB_FILE):
        return []
    all_extracted, _ = mt.load_all_records_from_db(mt.DB_FILE)
    return sorted(
        {r["semester_label"] for r in all_extracted if r["enrollment"] is not None},
        key=lambda s: mt.SEMESTER_NAMES.index(s) if s in mt.SEMESTER_NAMES else 999,
    )


def _k7c_ensure_draft_loaded():
    """Lazily seed the draft dropdowns from whatever's currently saved
    globally (or the K-scheme defaults), the first time the K7 (Part C)
    tile is shown in a session, so the picker opens pre-filled with the
    values that will actually be used rather than blank."""
    if state["k7c_level1_draft"] is None and state["k7c_fa_draft"] is None and state["k7c_sa_draft"] is None:
        labels = mt.load_k7c_labels(mt.DB_FILE)
        state["k7c_level1_draft"] = labels["level1"]
        state["k7c_fa_draft"] = labels["fa"]
        state["k7c_sa_draft"] = labels["sa"]
    if state["k7c_reference_semester"] is None:
        semesters = get_semesters_in_db()
        if semesters:
            state["k7c_reference_semester"] = semesters[0]


def on_k7c_reference_change(e):
    state["k7c_reference_semester"] = e.value
    render_mode_content()


def on_k7c_level1_change(e):
    state["k7c_level1_draft"] = e.value
    # Level 2 choices are scoped to the chosen Level 1 branch, so any
    # previously-picked FA/SA no longer under this branch must be cleared.
    state["k7c_fa_draft"] = None
    state["k7c_sa_draft"] = None
    render_mode_content()


def on_k7c_fa_change(e):
    state["k7c_fa_draft"] = e.value


def on_k7c_sa_change(e):
    state["k7c_sa_draft"] = e.value


def save_k7c_mapping():
    level1, fa, sa = state["k7c_level1_draft"], state["k7c_fa_draft"], state["k7c_sa_draft"]
    if not level1 or not fa or not sa:
        ui.notify("Pick a Level 1 and both Level 2 equivalents before saving.", type="warning")
        return
    if fa == sa:
        ui.notify("The two Level 2 equivalents can't be the same column.", type="warning")
        return
    mt.save_k7c_labels(level1, fa, sa, mt.DB_FILE)
    ui.notify(
        "Saved -- K7 (Part C) will use these labels for every semester.", type="positive",
    )
    render_mode_content()


def render_k7c_equivalence_block():
    """Rendered inside the K7 (Part C) tile: ONE global Level 1 dropdown
    and two Level 2 dropdowns (FA equivalent, SA equivalent, scoped to
    the chosen Level 1 branch). Options are read from whichever semester
    is picked as the reference; the saved choice then applies identically
    to every semester when the report is generated -- scheme-agnostic,
    no per-semester detection or blocking."""
    semesters = get_semesters_in_db()
    if not semesters:
        return
    _k7c_ensure_draft_loaded()

    reference = state["k7c_reference_semester"] or semesters[0]
    level1_options, level2_by_level1 = mt.get_k7c_level_options(reference, mt.DB_FILE)
    level2_options = level2_by_level1.get(state["k7c_level1_draft"], []) if state["k7c_level1_draft"] else []
    saved = mt.load_k7c_labels(mt.DB_FILE)
    is_saved = (
        state["k7c_level1_draft"] == saved["level1"]
        and state["k7c_fa_draft"] == saved["fa"]
        and state["k7c_sa_draft"] == saved["sa"]
    )

    with ui.column().classes("gap-1 mt-1 w-full"):
        ui.label(
            "Which trained columns are the Theory-vs-internal-exam comparison? "
            "Pick once -- applied to every semester."
        ).classes("text-xs text-gray-500")

        with ui.row().classes("items-center gap-2 mt-1 flex-wrap"):
            ui.label("Get options from:").classes("text-xs w-32")
            ui.select(
                semesters, value=reference, on_change=on_k7c_reference_change,
            ).classes("w-40").props("dense outlined")

        with ui.row().classes("items-center gap-2 mt-1 flex-wrap"):
            ui.label("Level 1:").classes("text-xs w-32")
            ui.select(
                level1_options, value=state["k7c_level1_draft"], on_change=on_k7c_level1_change,
            ).classes("w-40").props("dense outlined")
        with ui.row().classes("items-center gap-2 mt-1 flex-wrap"):
            ui.label("Level 2 (FA-TH):").classes("text-xs w-32")
            ui.select(
                level2_options, value=state["k7c_fa_draft"], on_change=on_k7c_fa_change,
            ).classes("w-40").props("dense outlined").set_enabled(bool(state["k7c_level1_draft"]))
        with ui.row().classes("items-center gap-2 mt-1 flex-wrap"):
            ui.label("Level 2 (SA-TH):").classes("text-xs w-32")
            ui.select(
                level2_options, value=state["k7c_sa_draft"], on_change=on_k7c_sa_change,
            ).classes("w-40").props("dense outlined").set_enabled(bool(state["k7c_level1_draft"]))

        with ui.row().classes("items-center gap-2 mt-1"):
            ui.button(
                "Save mapping", icon="save", on_click=save_k7c_mapping,
            ).props("dense outline color=primary")
            if is_saved:
                ui.icon("check_circle", color="positive").classes("text-sm")
                ui.label("Currently saved").classes("text-xs text-gray-500")


# Row keys shown in the left-hand list -- "yearly_result" stands in for
# the combined Yearly Result + Yearly Eligible/Non-Eligible row (see
# render_report_panel_content special-case below). Order mirrors
# REPORT_ORDER but with "yearly_eligibility" folded out.
REPORT_ROW_ORDER = [k for k in REPORT_ORDER if k != "yearly_eligibility"]

REPORT_ROW_LABELS = dict(REPORT_LABELS)
REPORT_ROW_LABELS["yearly_result"] = "Yearly Result Report & Eligible/Non-Eligible List"


def report_row_label(key):
    """Label shown for a report row/panel -- the Departmental Report carries the logged-in
    department's name."""
    if key == "departmental" and state.get("logged_in"):
        return f"Departmental Report -- {state['logged_in'].get('department_name', '')}"
    return REPORT_ROW_LABELS[key]


def _report_row_enabled(key):
    """Collapsed-row checkbox state. For the combined yearly row this
    reflects either underlying report being enabled."""
    sel = state["report_selection"]
    if key == "yearly_result":
        return sel["yearly_result"]["enabled"] or sel["yearly_eligibility"]["enabled"]
    return sel[key]["enabled"]


def _report_row_blocked(key):
    if key == "yearly_result" and state["yearly_report_mode"] != "simple":
        blocked, _status = mt.yearly_reports_are_blocked(mt.DB_FILE)
        return blocked
    return False


def toggle_report_panel(key):
    """Expand/collapse a report row's panel. Append-only ordering: newly
    opened reports go to the end of report_panel_open, existing ones are
    never force-closed by opening another."""
    open_list = state["report_panel_open"]
    if key in open_list:
        open_list.remove(key)
    else:
        open_list.append(key)
    render_report_panel(state["report_panel_container"])


def on_report_row_checkbox(e, key):
    """Collapsed-row checkbox: toggles inclusion in the PDF run without
    opening/closing the panel. For the combined yearly row this drives
    BOTH underlying reports together (each still has its own checkbox
    inside the expanded panel for fine control) -- EXCEPT in Option 1
    ("simple") mode, where Yearly Eligibility List has nothing to
    produce and stays off regardless."""
    sel = state["report_selection"]
    if key == "yearly_result":
        simple_mode = state["yearly_report_mode"] == "simple"
        if not simple_mode:
            blocked, _status = mt.yearly_reports_are_blocked(mt.DB_FILE)
            if blocked:
                e.sender.value = False
                return
        sel["yearly_result"]["enabled"] = e.value
        sel["yearly_eligibility"]["enabled"] = e.value and not simple_mode
    else:
        sel[key]["enabled"] = e.value
    # Refresh panel too, in case it's open and showing a stale checkbox.
    if key in state["report_panel_open"]:
        render_report_panel(state["report_panel_container"])


def render_report_row(key):
    """One collapsed row in the left list: checkbox + label + expand
    click zone. One report per line, per the new layout."""
    is_open = key in state["report_panel_open"]
    blocked = _report_row_blocked(key)
    enabled = _report_row_enabled(key)

    with ui.row().classes(
        "w-full items-center gap-2 py-2 px-3 rounded border "
        + ("border-primary bg-blue-50" if is_open else "border-gray-200")
    ):
        ui.checkbox(
            value=enabled,
            on_change=lambda e, k=key: on_report_row_checkbox(e, k),
        ).props(f"dense disable={'true' if blocked else 'false'}")

        with ui.row().classes("items-center gap-2 flex-grow cursor-pointer").on(
            "click", lambda k=key: toggle_report_panel(k)
        ):
            ui.label(report_row_label(key)).classes("text-sm font-medium")
            if blocked:
                ui.icon("warning", color="negative").classes("text-sm")

        ui.icon("expand_more" if not is_open else "expand_less").classes(
            "text-lg cursor-pointer"
        ).on("click", lambda k=key: toggle_report_panel(k))


def render_status_ticks(key):
    """Single-choice category picker for ONE report: one radio option per category
    actually present in the seating chart (exactly as typed), plus 'All combined'.
    Exactly one category is chosen per report -> one PDF (per semester where
    applicable). Nothing is chosen by default."""
    sel = state["report_selection"][key]
    cats = state["report_categories"]
    if not cats:
        ui.label("No categories found yet -- save the seating chart or extract data first.").classes(
            "text-xs text-orange-600"
        )
        return

    options = {c: c for c in cats}
    options["both"] = "All combined"
    current = sel["statuses"][0] if sel["statuses"] else None
    if current not in options:
        current = None
        sel["statuses"] = []

    def choose(e):
        sel["statuses"] = [e.value] if e.value else []
        if key == "departmental":
            _dept_rerender()  # the enrolled boxes follow the chosen category

    ui.label("Category (choose one):").classes("text-xs text-gray-600")
    ui.radio(options, value=current, on_change=choose).props("dense inline").classes("text-xs")


def _dept_rerender():
    render_report_panel(state["report_panel_container"])


def _dept_load_drafts(force=False):
    """(Re)load the Departmental Report setup drafts from the ACTIVE scheme's database -- once per
    scheme database, or whenever force=True (e.g. after saving classes changed the mapping)."""
    if not force and state["dept_loaded_key"] == mt.DB_FILE:
        return
    state["dept_classes_draft"] = [dict(c) for c in mt.load_dept_result_classes(mt.DB_FILE)]
    state["dept_mapping_draft"] = dict(mt.load_dept_result_mapping(mt.DB_FILE))
    state["dept_enrolled_draft"] = {k: str(v) for k, v in mt.load_dept_enrolled(mt.DB_FILE).items()}
    state["dept_program_code_draft"] = mt.load_dept_program_code(mt.DB_FILE)
    state["dept_sem_off_draft"] = set(mt.load_dept_semesters_off(mt.DB_FILE))
    state["dept_loaded_key"] = mt.DB_FILE


def render_departmental_setup():
    """Setup tables for the Departmental Report, shown inside its report panel. Everything is saved
    in the ACTIVE scheme's own database. Each table has its own Save button."""
    dept = state["logged_in"]
    if not os.path.exists(mt.DB_FILE):
        ui.label("No database for this scheme yet -- run Extract mode first.").classes("text-xs text-red-600")
        return
    _dept_load_drafts()
    saved_classes = mt.load_dept_result_classes(mt.DB_FILE)

    def _exp_open(n, default):
        return state["dept_open"].get(n, default)

    def _exp_set(n, v):
        state["dept_open"][n] = v

    ui.label(f"Department: {dept['department_name']}").classes("text-xs text-gray-600 mt-2")
    ui.checkbox(
        "Show percentage beside each result class, e.g. 12 (30%) -- of Total Appeared",
        value=state["report_selection"]["departmental"].get("show_pct", False),
        on_change=lambda e: state["report_selection"]["departmental"].update(show_pct=bool(e.value)),
    ).props("dense")
    ui.label(
        "Everything below is saved for THIS scheme only. Counts are never mixed between schemes or "
        "between categories (choose the category above)."
    ).classes("text-xs text-gray-500")

    blockers = mt.dept_report_blockers(mt.DB_FILE)
    if blockers:
        with ui.column().classes("gap-0 mt-1 bg-orange-50 border border-orange-300 rounded p-2 w-full"):
            ui.label("Not ready to generate yet:").classes("text-xs font-semibold text-orange-700")
            for b in blockers:
                ui.label(f"- {b}").classes("text-xs text-orange-700")
    else:
        with ui.row().classes("items-center gap-1 mt-1"):
            ui.icon("check_circle", color="positive").classes("text-sm")
            ui.label("Setup complete -- ready to generate.").classes("text-xs text-green-700")

    # ---------------- 1. Result classes ----------------
    with ui.expansion(
        "1. Result Classes", icon="category", value=_exp_open(1, not saved_classes),
        on_value_change=lambda e: _exp_set(1, e.value),
    ).classes("w-full border rounded mt-2"):
        ui.label(
            "Type each class name (e.g. FIRST CLASS, SECOND CLASS, DISTINCTION, PASS (CLEAR), ATKT, FAIL). "
            "Tick \"counts toward Total Pass\" for the classes that make up the Total column. Click Save "
            "classes -- the mapping table below only offers SAVED classes."
        ).classes("text-xs text-gray-500")

        def add_class():
            state["dept_classes_draft"].append({"id": None, "name": "", "counts_pass": False})
            _dept_rerender()

        def remove_class(c):
            state["dept_classes_draft"].remove(c)
            _dept_rerender()

        for c in state["dept_classes_draft"]:
            with ui.row().classes("items-center gap-2 w-full flex-nowrap"):
                ui.input(
                    value=c["name"], placeholder="Class name",
                    on_change=lambda e, cc=c: cc.update(name=e.value or ""),
                ).props("dense outlined").classes("flex-grow")
                ui.checkbox(
                    "counts toward Total Pass", value=c["counts_pass"],
                    on_change=lambda e, cc=c: cc.update(counts_pass=bool(e.value)),
                ).props("dense")
                ui.button(icon="delete", on_click=lambda cc=c: remove_class(cc)).props(
                    "flat dense round color=negative"
                )

        def save_classes():
            names = [(c["name"] or "").strip() for c in state["dept_classes_draft"]]
            if any(not n for n in names):
                ui.notify("Every class needs a name (or delete the empty box).", type="warning")
                return
            if len({n.lower() for n in names}) != len(names):
                ui.notify("Class names must be unique.", type="warning")
                return
            state["dept_classes_draft"] = [dict(c) for c in mt.save_dept_result_classes(
                state["dept_classes_draft"], mt.DB_FILE)]
            state["dept_mapping_draft"] = dict(mt.load_dept_result_mapping(mt.DB_FILE))
            ui.notify(f"Saved {len(names)} result class(es).", type="positive")
            _dept_rerender()

        with ui.row().classes("gap-2 mt-2"):
            ui.button("Add class", icon="add", on_click=add_class).props("outline dense")
            ui.button("Save classes", icon="save", on_click=save_classes).props("unelevated color=primary dense")

    # ---------------- 2. Result -> class mapping ----------------
    unique_results = mt.list_unique_results(mt.DB_FILE)
    class_options = {c["id"]: c["name"] for c in saved_classes}
    mapped_n = sum(1 for r in unique_results if state["dept_mapping_draft"].get(r) in class_options)
    with ui.expansion(
        f"2. Result Mapping -- {mapped_n} of {len(unique_results)} assigned", icon="rule",
        value=_exp_open(2, bool(saved_classes) and mapped_n < len(unique_results)),
        on_value_change=lambda e: _exp_set(2, e.value),
    ).classes("w-full border rounded mt-2"):
        if not saved_classes:
            ui.label("Define and save at least one result class first.").classes("text-xs text-orange-600")
        elif not unique_results:
            ui.label("No Result values found in this scheme's database yet.").classes("text-xs text-gray-500")
        else:
            ui.label(
                "Every distinct Result found across all semesters of this scheme. Choose the class each "
                "one is grouped under."
            ).classes("text-xs text-gray-500")

            def set_mapping(result, value):
                state["dept_mapping_draft"][result] = value

            for res in unique_results:
                cur = state["dept_mapping_draft"].get(res)
                with ui.row().classes("items-center gap-2 w-full flex-nowrap"):
                    ui.label(res).classes("text-sm w-72 flex-shrink-0")
                    ui.select(
                        class_options, value=cur if cur in class_options else None,
                        on_change=lambda e, r=res: set_mapping(r, e.value),
                    ).props("dense outlined clearable").classes("w-64")

            def save_mapping():
                clean = {r: state["dept_mapping_draft"].get(r) for r in unique_results
                         if state["dept_mapping_draft"].get(r) in class_options}
                mt.save_dept_result_mapping(clean, mt.DB_FILE)
                state["dept_mapping_draft"] = dict(clean)
                left = len(unique_results) - len(clean)
                ui.notify(
                    "Mapping saved." if not left else f"Mapping saved -- {left} Result value(s) still unassigned.",
                    type="positive" if not left else "warning",
                )
                _dept_rerender()

            ui.button("Save mapping", icon="save", on_click=save_mapping).props(
                "unelevated color=primary dense"
            ).classes("mt-2")

    # ---------------- 3. Program code + semesters + enrolled students ----------------
    semesters = get_semesters_in_db()
    cats_by_sem = mt.get_dept_semester_categories()
    chosen = (state["report_selection"]["departmental"]["statuses"] or [None])[0]
    with ui.expansion(
        "3. Program Code & Enrolled Students", icon="groups", value=_exp_open(3, False),
        on_value_change=lambda e: _exp_set(3, e.value),
    ).classes("w-full border rounded mt-2"):
        def on_program_code(e):
            state["dept_program_code_draft"] = e.value or ""

        ui.input(
            label="Program Code (e.g. TX)", value=state["dept_program_code_draft"], on_change=on_program_code,
        ).props("dense outlined").classes("w-48")

        ui.label(
            "Tick the semesters to include in the report, and enter the number of enrolled students for "
            "the category chosen above."
        ).classes("text-xs text-gray-500 mt-2")
        if chosen is None:
            ui.label("Choose a category above to enter enrolled students.").classes("text-xs text-orange-600")
        elif chosen == "both":
            ui.label("All combined: enter each category's number -- the report uses their sum.").classes(
                "text-xs text-gray-500"
            )
        else:
            ui.label(f"Category: {chosen}").classes("text-xs text-gray-500")
        if not semesters:
            ui.label("No semesters with data yet.").classes("text-xs text-gray-500")

        def toggle_sem(sem, ticked):
            if ticked:
                state["dept_sem_off_draft"].discard(sem)
            else:
                state["dept_sem_off_draft"].add(sem)
            _dept_rerender()

        for sem in semesters:
            ticked = sem not in state["dept_sem_off_draft"]
            cats = cats_by_sem.get(sem, [])
            with ui.row().classes("items-center gap-2 w-full"):
                ui.checkbox(
                    sem.title(), value=ticked, on_change=lambda e, s=sem: toggle_sem(s, e.value),
                ).props("dense").classes("w-48 flex-shrink-0 text-sm font-medium")
                if not ticked or chosen is None:
                    continue
                show_cats = cats if chosen == "both" else ([chosen] if chosen in cats else [])
                if not show_cats:
                    ui.label(
                        "no seating-chart categories for this semester" if chosen == "both"
                        else f"no {chosen} students in the seating chart"
                    ).classes("text-xs text-orange-600")
                for cat in show_cats:
                    def on_enrolled(e, k=(sem, cat)):
                        state["dept_enrolled_draft"][k] = e.value or ""

                    ui.input(
                        label=cat, value=state["dept_enrolled_draft"].get((sem, cat), ""), on_change=on_enrolled,
                    ).props("dense outlined type=number").classes("w-28")

        def save_enrolled():
            values = {}
            for (sem, cat), raw in state["dept_enrolled_draft"].items():
                raw = (raw or "").strip()
                if not raw:
                    continue
                try:
                    n = int(float(raw))
                except ValueError:
                    ui.notify(f"{sem.title()} / {cat}: '{raw}' is not a number.", type="warning")
                    return
                if n < 0:
                    ui.notify(f"{sem.title()} / {cat}: cannot be negative.", type="warning")
                    return
                values[(sem, cat)] = n
            mt.save_dept_program_code(state["dept_program_code_draft"], mt.DB_FILE)
            mt.save_dept_enrolled(values, mt.DB_FILE)
            mt.save_dept_semesters_off(state["dept_sem_off_draft"], mt.DB_FILE)
            ui.notify("Program Code, semesters and enrolled students saved.", type="positive")
            _dept_rerender()

        ui.button("Save", icon="save", on_click=save_enrolled).props("unelevated color=primary dense").classes("mt-2")


def render_report_block(key, embedded=False):
    """Renders one report's status + any extra options (NOT the
    include-in-run checkbox -- that now lives on the collapsed row).
    Used inside the expanded right-panel content."""
    sel = state["report_selection"][key]

    yearly_blocked = False
    yearly_status = "clean"
    if key in ("yearly_result", "yearly_eligibility") and state["yearly_report_mode"] != "simple":
        yearly_blocked, yearly_status = mt.yearly_reports_are_blocked(mt.DB_FILE)
        if yearly_blocked and sel["enabled"]:
            sel["enabled"] = False  # force off while blocked, so Generate can't slip through

    def on_toggle(e, k=key):
        state["report_selection"][k]["enabled"] = e.value

    def _content():
        checkbox = ui.checkbox(
            REPORT_LABELS[key], value=sel["enabled"], on_change=on_toggle,
        ).classes("font-semibold text-sm")
        if key in ("yearly_result", "yearly_eligibility"):
            checkbox.props(f"disable={'true' if yearly_blocked else 'false'}")
            if yearly_blocked:
                with ui.row().classes("items-center gap-2 mt-1 ml-8"):
                    ui.icon("warning", color="negative").classes("text-sm")
                    ui.label(
                        "Run the Gap Check above first."
                        if yearly_status == "not_checked" else
                        "Missing-semester gaps on record -- upload a secondary database "
                        "above to fill them."
                    ).classes("text-xs text-red-600")
        with ui.column().classes("ml-8 gap-1"):
            render_status_ticks(key)

            if key == "k7_partb":
                def on_fail_threshold(e):
                    state["report_selection"]["k7_partb"]["fail_threshold"] = e.value or 0.0

                with ui.row().classes("items-center gap-2 mt-1"):
                    ui.label("Highlight Failed % above:").classes("text-xs")
                    ui.number(
                        value=sel["fail_threshold"], on_change=on_fail_threshold,
                    ).classes("w-20").props("dense outlined")
                    ui.label("%").classes("text-xs")

                filled = mt.course_codes_are_filled(mt.DB_FILE)
                with ui.row().classes("items-center gap-2 mt-1"):
                    ui.icon(
                        "check_circle" if filled else "warning",
                        color="positive" if filled else "negative",
                    ).classes("text-sm")
                    ui.label(
                        "Course codes entered" if filled
                        else "Course codes NOT entered yet -- required"
                    ).classes("text-xs")
                    if not filled:
                        ui.button(
                            "Go to Course Codes", on_click=lambda: select_mode("coursecodes"),
                        ).props("dense outline")

            if key == "k7_partc":
                render_k7c_equivalence_block()

            if key == "departmental":
                render_departmental_setup()

            if key == "bright_weak":
                def on_weak_threshold(e):
                    state["report_selection"]["bright_weak"]["weak_threshold"] = e.value or 0.0

                def on_bright_threshold(e):
                    state["report_selection"]["bright_weak"]["bright_threshold"] = e.value or 0.0

                with ui.row().classes("items-center gap-2 mt-1"):
                    ui.label("Weak: % below").classes("text-xs")
                    ui.number(
                        value=sel["weak_threshold"], on_change=on_weak_threshold,
                    ).classes("w-20").props("dense outlined")
                    ui.label("%").classes("text-xs")
                with ui.row().classes("items-center gap-2 mt-1"):
                    ui.label("Bright: % above").classes("text-xs")
                    ui.number(
                        value=sel["bright_threshold"], on_change=on_bright_threshold,
                    ).classes("w-20").props("dense outlined")
                    ui.label("%").classes("text-xs")

    if embedded:
        _content()
    else:
        with ui.card().classes("w-full"):
            _content()


def render_yearly_combined_panel():
    """Expanded-panel content for the combined Yearly Result Report +
    Yearly Eligible/Non-Eligible Student List row. Starts with an
    Option 1/Option 2 choice that switches everything else shown below
    it -- see state["yearly_report_mode"]."""
    ui.label("Yearly Result Report & Eligible/Non-Eligible List").classes(
        "font-semibold text-sm"
    )

    def on_mode_change(e):
        state["yearly_report_mode"] = "simple" if e.value == "Option 1" else "gap_check"
        if state["yearly_report_mode"] == "simple":
            # Eligibility List has nothing to produce in this mode (see
            # docstring) -- untick it so a stale selection can't sneak
            # into a Generate click while its checkbox is hidden.
            state["report_selection"]["yearly_eligibility"]["enabled"] = False
        render_report_panel(state["report_panel_container"])

    ui.radio(
        ["Option 1", "Option 2"],
        value="Option 1" if state["yearly_report_mode"] == "simple" else "Option 2",
        on_change=on_mode_change,
    ).props("inline")

    if state["yearly_report_mode"] == "simple":
        ui.label(
            "Option 1 -- No previous-database upload. Generates immediately from "
            "whatever semesters already exist, however incomplete a year is. Report "
            "shows each semester's own table side by side, WITHOUT the combined yearly "
            "aggregate columns (Failed Count / Average Marks / Eligible-Non-Eligible / "
            "Remark). No Gap Check, no missing-semester upload."
        ).classes("text-xs text-gray-500 mb-2")
        ui.label(
            "Yearly Eligible/Non-Eligible List is not available in this mode -- its "
            "entire output IS the yearly aggregate calculation this mode skips."
        ).classes("text-xs text-orange-600 mb-2")
        render_report_block("yearly_result", embedded=True)
    else:
        ui.label(
            "Option 2 -- True yearly result. Requires every enrollment's full year on "
            "record first (Gap Check below), with an optional secondary-database upload "
            "to fill in whatever's missing."
        ).classes("text-xs text-gray-500 mb-2")
        render_yearly_gap_check()
        ui.separator().classes("my-2")
        render_report_block("yearly_result", embedded=True)
        ui.separator().classes("my-2")
        render_report_block("yearly_eligibility", embedded=True)


def render_report_panel_content(key):
    """Dispatches to the right expanded-panel body for a report row key."""
    if key == "yearly_result":
        render_yearly_combined_panel()
    else:
        render_report_block(key, embedded=True)


def render_report_panel(container):
    """Right-hand panel: one card per currently-open report, stacked in
    the order they were opened (append order in report_panel_open).
    Rebuilt in place on every toggle."""
    container.clear()
    with container:
        open_list = state["report_panel_open"]
        if not open_list:
            with ui.column().classes("items-center justify-center w-full h-full text-gray-400 gap-2 py-16"):
                ui.icon("arrow_back", color="grey").classes("text-3xl")
                ui.label("Select a report on the left to configure it here.").classes("text-sm")
            return

        with ui.column().classes("w-full gap-4"):
            for key in open_list:
                with ui.card().classes("w-full"):
                    with ui.row().classes("w-full items-center justify-between"):
                        ui.label(report_row_label(key)).classes("text-base font-bold")
                        ui.button(
                            icon="close", on_click=lambda k=key: toggle_report_panel(k),
                        ).props("flat dense round size=sm")
                    ui.separator().classes("mb-2")
                    render_report_panel_content(key)


def render_report_select(container):
    state["report_categories"] = mt.list_report_categories(mt.DB_FILE) if os.path.exists(mt.DB_FILE) else []
    for _k, _sel in state["report_selection"].items():
        # drop ticks for categories that don't exist in this scheme
        _sel["statuses"] = [s for s in _sel["statuses"] if s == "both" or s in state["report_categories"]]
    with container:
        with ui.card().classes("w-full"):
            ui.label("Report").classes("text-xl font-bold")
            ui.label(MODE_DESCRIPTIONS["report"]).classes("text-sm text-gray-600")
            ui.label(
                "Report mode is GLOBAL -- it works across the whole database at once, "
                "with no scheme distinction at all."
            ).classes("text-xs text-gray-500 mt-1")
            if not os.path.exists(mt.DB_FILE):
                ui.separator()
                ui.label(
                    f"Could not find {mt.DB_FILE} -- run Extract mode at least once first."
                ).classes("text-sm text-red-600 mt-3")

        # One-per-line list on the left, expanding panel on the right.
        # Two independent scroll areas so scrolling the list never moves
        # the panel and vice versa. Kept side-by-side even on narrow
        # screens (no stacked/mobile layout switch).
        with ui.row().classes("w-full gap-4 items-start flex-nowrap mt-4"):
            with ui.column().classes(
                "gap-2 flex-shrink-0 w-full sm:w-[38%] max-h-[75vh] overflow-y-auto pr-1"
            ):
                for key in REPORT_ROW_ORDER:
                    render_report_row(key)

            panel_container = ui.column().classes(
                "flex-grow max-h-[75vh] overflow-y-auto pl-1 min-w-0"
            )
            state["report_panel_container"] = panel_container
            render_report_panel(panel_container)

        with ui.card().classes("w-full"):
            ui.button(
                "Generate", icon="picture_as_pdf", on_click=generate_reports,
            ).props("unelevated color=primary")


def render_report_generating(container):
    with container:
        with ui.card().classes("w-full"):
            ui.label("Generating reports...").classes("text-lg font-semibold")
            with ui.column().classes("gap-0 mt-2 font-mono"):
                for line in state["report_log"]:
                    ui.label(line).classes("text-xs")


def render_report_done(container):
    with container:
        with ui.card().classes("w-full"):
            ui.label("Reports generated!").classes("text-xl font-bold text-green-700")
            files = state["report_generated_files"]
            if not files:
                ui.label("No report files were produced.").classes("text-sm text-gray-500 mt-2")
            else:
                with ui.column().classes("gap-2 mt-3"):
                    for label, path in files:
                        with ui.row().classes("items-center gap-2 w-full"):
                            ui.icon("picture_as_pdf", color="red").classes("text-lg")
                            ui.label(label).classes("text-sm flex-grow")
                            ui.button(
                                "Download", icon="download",
                                on_click=lambda p=path, n=os.path.basename(path): ui.download(p, n),
                            ).props("dense outline")

            with ui.expansion("Build log", icon="article").classes("w-full text-xs mt-3"):
                with ui.column().classes("gap-0 font-mono"):
                    for line in state["report_log"]:
                        ui.label(line).classes("text-xs")

            with ui.row().classes("gap-2 mt-4"):
                ui.button(
                    "Build More Reports", icon="replay", on_click=reset_reports,
                ).props("outline")
                ui.button(
                    "Continue to Recheck Mode \u2192", icon="arrow_forward",
                    on_click=lambda: select_mode("recheck"),
                ).props("unelevated color=primary")


# =======================================================================
# RECHECK MODE
# =======================================================================
# For students whose marks changed after a rechecking application.
# Mirrors msbte_tool.py's run_recheck_mode(): choose Automatic (re-fetch
# live, same captcha flow as Extract, using the enrollment numbers
# pasted in the shared top textarea) or Manual (type corrected marks in
# yourself, one enrollment at a time, pre-filled with current DB
# values). Automatic reuses save_records_to_db()'s upsert so a
# corrected value just overwrites the old one in place; Manual issues a
# direct UPDATE on only the fields actually changed.

def reset_recheck_to_choose():
    state["recheck_step"] = "choose"
    state["recheck_log"] = []
    state["recheck_summary"] = None
    state["recheck_queue_mode"] = None
    state["recheck_queue_list"] = []
    state["recheck_queue_pos"] = 0
    state["recheck_queue_stats"] = {}
    state["recheck_queue_log"] = []
    state["recheck_manual_enrollment"] = ""
    state["recheck_manual_records"] = None
    state["recheck_manual_semesters"] = []
    state["recheck_manual_delete_semesters"] = set()
    state["recheck_delete_semesters_present"] = []
    render_mode_content()


async def start_recheck_automatic():
    enrollments = enrollment_lines()
    if not enrollments:
        ui.notify("Paste at least one enrollment number above first.", type="warning")
        return

    mapping = _load_mapping_or_none()
    if mapping is None:
        ui.notify(
            f"Could not find {mt.MAPPING_FILE}. Finish Train mode first.",
            type="negative",
        )
        return

    state["recheck_step"] = "automatic_running"
    state["recheck_log"] = []
    state["recheck_summary"] = None
    render_mode_content()

    session = requests.Session()
    changed = 0
    unchanged = 0
    failed = 0

    for enr in enrollments:
        _log(f"Fetching {enr} ...", "recheck_log")
        before = mt._snapshot_student_records(enr, mt.DB_FILE)
        try:
            html, attempts = await web_fetch_result_html_with_retry(
                session, enr, log_key="recheck_log"
            )
            if not html:
                _log("  Fetch/captcha failed. Skipping.", "recheck_log")
                failed += 1
                continue

            extracted, canonical_rows, subjectwise_records, review = mt.apply_mapping_to_html(
                html, mapping, enr, mt.DB_FILE
            )
            if not extracted and not canonical_rows and not subjectwise_records:
                _log(
                    "  No data extracted (wrong enrollment number, no mapping for this "
                    "semester, or no result available). Skipping.",
                    "recheck_log",
                )
                failed += 1
                continue

            mt.save_records_to_db(extracted, review, mt.DB_FILE)
            mt.save_canonical_marks_to_db(canonical_rows, mt.DB_FILE)
            mt.save_subjectwise_student_records_to_db(subjectwise_records, mt.DB_FILE)
            after = mt._snapshot_student_records(enr, mt.DB_FILE)
            diff_keys = {k for k in after if before.get(k) != after.get(k)}

            if diff_keys:
                changed += 1
                _log(f"  Updated: {len(diff_keys)} field(s) changed.", "recheck_log")
            else:
                unchanged += 1
                _log(
                    "  No change detected -- MSBTE may not have updated this result yet. "
                    "Consider Manual for this one.",
                    "recheck_log",
                )
        except Exception as e:
            _log(f"  ERROR processing {enr}: {e}. Skipping and continuing.", "recheck_log")
            failed += 1

    if changed:
        invalidate_downstream_data()

    state["recheck_summary"] = {
        "total": len(enrollments), "changed": changed, "unchanged": unchanged, "failed": failed,
    }
    state["recheck_step"] = "automatic_done"
    render_mode_content()


# -----------------------------------------------------------------------
# MANUAL / DELETE QUEUE -- shared machinery
# -----------------------------------------------------------------------
# Both Manual recheck and Delete now walk the SAME pasted enrollment list
# (the shared top textarea) sequentially, one enrollment at a time,
# rather than asking the user to retype each enrollment number. The list
# is snapshotted into recheck_queue_list the moment the run starts, so
# editing the shared textarea mid-run never reshuffles a queue already
# in progress. Any enrollment with no data at all in the database is
# skipped automatically (logged as "not_found") rather than dead-ending
# the run.
#
# recheck_manual_enrollment / recheck_manual_records / _semesters /
# _subject_names / _components / _values / _originals /
# _subjectwise_values / _subjectwise_originals / _subjectwise_meta hold
# the CURRENT queue item's editable state for Manual (same shape as
# before, just reloaded per queue position instead of per typed lookup).
# recheck_delete_semesters_present / recheck_manual_delete_semesters
# hold the current queue item's state for Delete.
#
# NOTE: "Back" reloads an earlier queue position for review/re-action
# but does not remove that position's earlier log entry/stat -- acting
# on it again (e.g. Save & Next a second time) logs a second entry. This
# only affects the summary counts's exact bookkeeping if you deliberately
# go back and re-save/re-delete the same enrollment twice in one run.

def _query_semesters_present(enrollment):
    """Sorted union of semester_label across student_records and
    subjectwise_student_records for one enrollment."""
    conn = sqlite3.connect(mt.DB_FILE)
    conn.row_factory = sqlite3.Row
    sems = {
        r["semester_label"] for r in
        conn.execute("SELECT DISTINCT semester_label FROM student_records WHERE enrollment = ?", (enrollment,))
    }
    try:
        sems |= {
            r["semester_label"] for r in
            conn.execute(
                "SELECT DISTINCT semester_label FROM subjectwise_student_records WHERE enrollment = ?",
                (enrollment,),
            )
        }
    except sqlite3.OperationalError:
        pass
    conn.close()
    return sorted(sems, key=lambda s: mt.SEMESTER_NAMES.index(s) if s in mt.SEMESTER_NAMES else 999)


def _load_manual_queue_item(enrollment):
    """Populates recheck_manual_* editor state for one enrollment, same
    data shape the old single-lookup Manual editor used. Returns False
    (state left untouched) if this enrollment has no data at all."""
    if not os.path.exists(mt.DB_FILE):
        return False

    conn = sqlite3.connect(mt.DB_FILE)
    conn.row_factory = sqlite3.Row
    records = conn.execute(
        "SELECT * FROM student_records WHERE enrollment = ? "
        "ORDER BY semester_label, group_name, abs_row, abs_col",
        (enrollment,),
    ).fetchall()
    try:
        subjectwise_rows = conn.execute(
            "SELECT * FROM subjectwise_student_records WHERE enrollment = ? "
            "ORDER BY semester_label, subject_index, node_id, role",
            (enrollment,),
        ).fetchall()
    except sqlite3.OperationalError:
        subjectwise_rows = []
    conn.close()

    if not records and not subjectwise_rows:
        return False

    semesters_present = sorted(
        {r["semester_label"] for r in records} | {r["semester_label"] for r in subjectwise_rows},
        key=lambda s: mt.SEMESTER_NAMES.index(s) if s in mt.SEMESTER_NAMES else 999,
    )

    heading_conn = sqlite3.connect(mt.DB_FILE)
    heading_conn.row_factory = sqlite3.Row
    heading_rows = heading_conn.execute(
        "SELECT * FROM semester_headings WHERE semester_label IN ({}) "
        "AND group_name IN ('subjects', 'thprsla')".format(
            ",".join("?" * len(semesters_present))
        ),
        semesters_present,
    ).fetchall()
    heading_conn.close()

    subject_name_by_sem_row = {}
    component_by_sem_col = {}
    for r in heading_rows:
        if r["group_name"] == "subjects":
            subject_name_by_sem_row[(r["semester_label"], r["abs_row"])] = r["value"]
        else:
            component_by_sem_col[(r["semester_label"], r["abs_col"])] = (r["value"] or "").strip()

    values = {}
    for r in records:
        if r["group_name"] == "obtained_marks" or r["group_name"] in mt.SUMMARY_GROUPS:
            key = (r["semester_label"], r["group_name"], r["abs_row"], r["abs_col"])
            values[key] = r["value"] or ""

    subjectwise_values = {}
    subjectwise_meta = {}
    for r in subjectwise_rows:
        key = (r["semester_label"], r["subject_index"], r["node_id"], r["role"])
        subjectwise_values[key] = r["value"] or ""
        subjectwise_meta[key] = {
            "subject_name": r["subject_name"],
            "component_label": r["component_label"],
        }

    state["recheck_manual_enrollment"] = enrollment
    state["recheck_manual_records"] = records
    state["recheck_manual_semesters"] = semesters_present
    state["recheck_manual_subject_names"] = subject_name_by_sem_row
    state["recheck_manual_components"] = component_by_sem_col
    state["recheck_manual_values"] = values
    state["recheck_manual_originals"] = dict(values)
    state["recheck_manual_subjectwise_values"] = subjectwise_values
    state["recheck_manual_subjectwise_originals"] = dict(subjectwise_values)
    state["recheck_manual_subjectwise_meta"] = subjectwise_meta
    return True


def _load_delete_queue_item(enrollment):
    """Populates recheck_manual_enrollment + recheck_delete_semesters_present
    for one enrollment. Returns False if it has no semesters to show."""
    if not os.path.exists(mt.DB_FILE):
        return False
    semesters = _query_semesters_present(enrollment)
    if not semesters:
        return False
    state["recheck_manual_enrollment"] = enrollment
    state["recheck_delete_semesters_present"] = semesters
    state["recheck_manual_delete_semesters"] = set()
    return True


def _load_queue_item(mode, enrollment):
    if mode == "manual":
        return _load_manual_queue_item(enrollment)
    return _load_delete_queue_item(enrollment)


def advance_recheck_queue():
    """Loads the queue item at the current position, auto-skipping (and
    logging as not_found) any enrollment with no data, until a real item
    is found or the queue is exhausted."""
    mode = state["recheck_queue_mode"]
    queue = state["recheck_queue_list"]
    while state["recheck_queue_pos"] < len(queue):
        enrollment = queue[state["recheck_queue_pos"]]
        if _load_queue_item(mode, enrollment):
            state["recheck_step"] = "queue_manual_editor" if mode == "manual" else "queue_delete_editor"
            render_mode_content()
            return
        state["recheck_queue_stats"]["not_found"] = state["recheck_queue_stats"].get("not_found", 0) + 1
        state["recheck_queue_log"].append(
            {"enrollment": enrollment, "status": "not_found", "detail": "no data in database"}
        )
        state["recheck_queue_pos"] += 1

    state["recheck_step"] = "queue_manual_done" if mode == "manual" else "queue_delete_done"
    render_mode_content()


def recheck_queue_back():
    """Steps back to the nearest earlier queue position that has data,
    for review or re-action. Does not touch stats/log."""
    mode = state["recheck_queue_mode"]
    queue = state["recheck_queue_list"]
    pos = state["recheck_queue_pos"] - 1
    while pos >= 0:
        if _load_queue_item(mode, queue[pos]):
            state["recheck_queue_pos"] = pos
            render_mode_content()
            return
        pos -= 1
    ui.notify("No earlier processable enrollment to go back to.", type="info")


def start_manual_recheck_queue():
    enrollments = enrollment_lines()
    if not enrollments:
        ui.notify("Paste at least one enrollment number in the shared box above first.", type="warning")
        return
    if not os.path.exists(mt.DB_FILE):
        ui.notify(f"Could not find {mt.DB_FILE}. Run Extract mode first.", type="negative")
        return
    state["recheck_queue_mode"] = "manual"
    state["recheck_queue_list"] = enrollments
    state["recheck_queue_pos"] = 0
    state["recheck_queue_stats"] = {"saved": 0, "skipped": 0, "not_found": 0}
    state["recheck_queue_log"] = []
    advance_recheck_queue()


def start_delete_recheck_queue():
    enrollments = enrollment_lines()
    if not enrollments:
        ui.notify("Paste at least one enrollment number in the shared box above first.", type="warning")
        return
    if not os.path.exists(mt.DB_FILE):
        ui.notify(f"Could not find {mt.DB_FILE}. Run Extract mode first.", type="negative")
        return
    state["recheck_queue_mode"] = "delete"
    state["recheck_queue_list"] = enrollments
    state["recheck_queue_pos"] = 0
    state["recheck_queue_stats"] = {"deleted": 0, "skipped": 0, "not_found": 0}
    state["recheck_queue_log"] = []
    advance_recheck_queue()


def recheck_queue_manual_save_and_next():
    enrollment = state["recheck_manual_enrollment"]
    values = state["recheck_manual_values"]
    originals = state["recheck_manual_originals"]
    sw_values = state["recheck_manual_subjectwise_values"]
    sw_originals = state["recheck_manual_subjectwise_originals"]

    changed = [
        (
            key[0], key[1], key[2], key[3],
            mt.normalize_obtained_total_marks((values.get(key) or "").strip())
            if key[1] == "obtained_total_marks" else (values.get(key) or "").strip(),
        )
        for key in originals
        if (values.get(key) or "").strip() != (originals.get(key) or "").strip()
    ]
    sw_changed = [
        (key[0], key[1], key[2], key[3], (sw_values.get(key) or "").strip())
        for key in sw_originals
        if (sw_values.get(key) or "").strip() != (sw_originals.get(key) or "").strip()
    ]

    if changed or sw_changed:
        conn = sqlite3.connect(mt.DB_FILE)
        if changed:
            conn.executemany(
                "UPDATE student_records SET value = ? "
                "WHERE enrollment = ? AND semester_label = ? AND group_name = ? "
                "AND abs_row = ? AND abs_col = ?",
                [(new_val, enrollment, sem, group, abs_row, abs_col)
                 for sem, group, abs_row, abs_col, new_val in changed],
            )
        if sw_changed:
            conn.executemany(
                "UPDATE subjectwise_student_records SET value = ? "
                "WHERE enrollment = ? AND semester_label = ? AND subject_index = ? "
                "AND node_id = ? AND role = ?",
                [(new_val, enrollment, sem, subject_index, node_id, role)
                 for sem, subject_index, node_id, role, new_val in sw_changed],
            )
        conn.commit()
        conn.close()

        done_count = len(changed) + len(sw_changed)
        invalidate_report_and_coursecode_caches()
        state["recheck_queue_stats"]["saved"] += 1
        state["recheck_queue_log"].append(
            {"enrollment": enrollment, "status": "saved", "detail": f"{done_count} field(s) updated"}
        )
        ui.notify(f"Saved {done_count} field(s) for {enrollment}.", type="positive")
    else:
        state["recheck_queue_stats"]["skipped"] += 1
        state["recheck_queue_log"].append(
            {"enrollment": enrollment, "status": "skipped", "detail": "no changes made"}
        )
        ui.notify(f"No changes for {enrollment} -- moving on.", type="info")

    state["recheck_queue_pos"] += 1
    advance_recheck_queue()


def recheck_queue_manual_skip():
    enrollment = state["recheck_manual_enrollment"]
    state["recheck_queue_stats"]["skipped"] += 1
    state["recheck_queue_log"].append(
        {"enrollment": enrollment, "status": "skipped", "detail": "skipped by user"}
    )
    state["recheck_queue_pos"] += 1
    advance_recheck_queue()


def recheck_queue_delete_confirm_and_next():
    enrollment = state["recheck_manual_enrollment"]
    to_delete = sorted(
        state["recheck_manual_delete_semesters"],
        key=lambda s: mt.SEMESTER_NAMES.index(s) if s in mt.SEMESTER_NAMES else 999,
    )
    if not to_delete:
        ui.notify("Tick at least one semester to delete, or use Skip.", type="warning")
        return

    def do_delete():
        dialog.close()
        counts = mt.delete_result_semesters(enrollment, to_delete, mt.DB_FILE)
        invalidate_report_and_coursecode_caches()
        detail = (
            f"{', '.join(s.title() for s in to_delete)} -- "
            f"{counts['student_records']} record row(s), "
            f"{counts['canonical_marks']} canonical mark row(s)"
        )
        if counts["yearly_gap_flags"]:
            detail += f", {counts['yearly_gap_flags']} yearly-gap flag(s) cleared"
        state["recheck_queue_stats"]["deleted"] += 1
        state["recheck_queue_log"].append({"enrollment": enrollment, "status": "deleted", "detail": detail})
        ui.notify(f"Deleted for {enrollment} -- {detail}", type="positive")
        state["recheck_queue_pos"] += 1
        advance_recheck_queue()

    with ui.dialog() as dialog, ui.card():
        ui.label(f"Delete data for {enrollment}?").classes("text-md font-bold text-red-700")
        ui.label(
            "This permanently removes the following semester(s) for this "
            "enrollment only -- other semesters, and all other enrollments, "
            "are untouched:"
        ).classes("text-sm mt-1")
        for s in to_delete:
            ui.label(f"- {s.title()}").classes("text-sm font-semibold ml-2")
        ui.label(
            "If this breaks a Yearly result pairing, re-import the missing "
            "semester later (CSV Import or online Train) to fix it."
        ).classes("text-xs text-gray-500 mt-2")
        with ui.row().classes("gap-2 mt-4"):
            ui.button("Delete", icon="delete_forever", on_click=do_delete).props(
                "unelevated color=negative"
            )
            ui.button("Cancel", on_click=dialog.close).props("outline")
    dialog.open()


def recheck_queue_delete_skip():
    enrollment = state["recheck_manual_enrollment"]
    state["recheck_queue_stats"]["skipped"] += 1
    state["recheck_queue_log"].append(
        {"enrollment": enrollment, "status": "skipped", "detail": "no deletion"}
    )
    state["recheck_queue_pos"] += 1
    advance_recheck_queue()


def render_recheck_choose(container):
    with container:
        with ui.card().classes("w-full"):
            ui.label("Recheck").classes("text-xl font-bold")
            ui.label(MODE_DESCRIPTIONS["recheck"]).classes("text-sm text-gray-600")
            if not os.path.exists(mt.DB_FILE):
                ui.separator()
                ui.label(
                    f"Could not find {mt.DB_FILE} -- run Extract mode at least once first."
                ).classes("text-sm text-red-600 mt-3")

        with ui.element("div").classes("w-full grid grid-cols-1 sm:grid-cols-3 gap-4"):
            n = len(enrollment_lines())

            with ui.card().classes("w-full"):
                ui.icon("cloud_download", color="primary").classes("text-2xl")
                ui.label("Automatic").classes("font-semibold")
                ui.label(
                    "Re-fetches each enrollment's result live from the MSBTE website (captcha "
                    "entry, same as Extract mode) and overwrites the old marks. Simplest, but "
                    "only works if MSBTE has already updated the result on their end -- if "
                    "not, nothing will look wrong, it'll just silently keep the old marks."
                ).classes("text-xs text-gray-600 mt-1")
                ui.label(f"{n} enrollment number(s) currently pasted above.").classes(
                    "text-xs mt-2"
                )
                ui.button(
                    "Start Automatic Recheck", icon="cloud_download",
                    on_click=start_recheck_automatic,
                ).classes("mt-3").props("unelevated color=primary").set_enabled(n > 0)

            with ui.card().classes("w-full"):
                ui.icon("edit", color="primary").classes("text-2xl")
                ui.label("Manual").classes("font-semibold")
                ui.label(
                    "Type the corrected marks in yourself. Steps through the SAME pasted "
                    "enrollment list above, one student at a time, pre-filled with current "
                    "database values -- always reliable regardless of whether MSBTE's site "
                    "has caught up."
                ).classes("text-xs text-gray-600 mt-1")
                ui.label(f"{n} enrollment number(s) currently pasted above.").classes(
                    "text-xs mt-2"
                )
                ui.button(
                    "Start Manual Recheck", icon="edit", on_click=start_manual_recheck_queue,
                ).classes("mt-3").props("unelevated color=primary").set_enabled(n > 0)

            with ui.card().classes("w-full border-2 border-red-200"):
                ui.icon("delete_forever", color="negative").classes("text-2xl")
                ui.label("Delete").classes("font-semibold text-red-700")
                ui.label(
                    "Permanently removes result data for specific semester(s) of specific "
                    "enrollment(s) -- steps through the SAME pasted list above, one student "
                    "at a time, letting you tick which semester(s) of each to wipe. Does not "
                    "touch Seating Chart data."
                ).classes("text-xs text-gray-600 mt-1")
                ui.label(f"{n} enrollment number(s) currently pasted above.").classes(
                    "text-xs mt-2"
                )
                ui.button(
                    "Start Delete", icon="delete_forever", on_click=start_delete_recheck_queue,
                ).classes("mt-3").props("unelevated color=negative").set_enabled(n > 0)


def render_recheck_automatic_running(container):
    with container:
        with ui.card().classes("w-full"):
            ui.label("Recheck (Automatic) in progress...").classes("text-lg font-semibold")
            ui.label("Solve each captcha as it appears below.").classes("text-xs text-gray-500")
            with ui.column().classes("gap-0 mt-2 font-mono"):
                for line in state["recheck_log"]:
                    ui.label(line).classes("text-xs")
        render_captcha_box(container)


def render_recheck_automatic_done(container):
    summary = state["recheck_summary"] or {}
    with container:
        with ui.card().classes("w-full"):
            ui.label("Recheck (Automatic) complete!").classes("text-xl font-bold text-green-700")
            with ui.grid(columns=2).classes("gap-x-6 gap-y-1 mt-3 text-sm"):
                ui.label("Enrollment numbers submitted:")
                ui.label(str(summary.get("total", 0))).classes("font-semibold")
                ui.label("Updated (changed):")
                ui.label(str(summary.get("changed", 0))).classes("font-semibold text-green-700")
                ui.label("No change detected:")
                ui.label(str(summary.get("unchanged", 0))).classes(
                    "font-semibold" + (" text-orange-600" if summary.get("unchanged") else "")
                )
                ui.label("Failed / skipped:")
                ui.label(str(summary.get("failed", 0))).classes(
                    "font-semibold" + (" text-red-600" if summary.get("failed") else "")
                )
            if summary.get("unchanged"):
                ui.label(
                    "For enrollments with no change detected, either re-run this later once "
                    "MSBTE's site has updated, or use Manual instead."
                ).classes("text-xs text-gray-600 mt-2")

            with ui.expansion("Log", icon="article").classes("w-full text-xs mt-3"):
                with ui.column().classes("gap-0 font-mono"):
                    for line in state["recheck_log"]:
                        ui.label(line).classes("text-xs")

            with ui.row().classes("gap-2 mt-4"):
                ui.button(
                    "Recheck More (Automatic)", icon="replay", on_click=reset_recheck_to_choose,
                ).props("outline")
                ui.button(
                    "Switch to Manual", icon="edit", on_click=start_manual_recheck_queue,
                ).props("outline")
                ui.button(
                    "Mark Complete", icon="check_circle",
                    on_click=lambda: mark_complete_and_advance("recheck"),
                ).props("unelevated color=positive")


def render_recheck_queue_progress(mode):
    queue = state["recheck_queue_list"]
    pos = state["recheck_queue_pos"]
    stats = state["recheck_queue_stats"]
    if mode == "manual":
        stats_text = f"{stats.get('saved', 0)} saved, {stats.get('skipped', 0)} skipped, {stats.get('not_found', 0)} not found"
    else:
        stats_text = f"{stats.get('deleted', 0)} deleted, {stats.get('skipped', 0)} skipped, {stats.get('not_found', 0)} not found"
    ui.label(f"Enrollment {pos + 1} of {len(queue)}  --  {stats_text}").classes(
        "text-xs text-gray-500 font-semibold"
    )


def render_recheck_queue_manual_editor(container):
    enrollment = state["recheck_manual_enrollment"]
    records = state["recheck_manual_records"] or []
    semesters_present = state["recheck_manual_semesters"]
    subject_name_by_sem_row = state["recheck_manual_subject_names"]
    component_by_sem_col = state["recheck_manual_components"]
    values = state["recheck_manual_values"]
    sw_values = state["recheck_manual_subjectwise_values"]
    sw_meta = state["recheck_manual_subjectwise_meta"]

    def on_value_change(e, key):
        values[key] = e.value

    def on_sw_value_change(e, key):
        sw_values[key] = e.value

    with container:
        with ui.card().classes("w-full"):
            render_recheck_queue_progress("manual")
            ui.label(f"Update Marks After Rechecking -- Enrollment {enrollment}").classes(
                "text-lg font-semibold mt-1"
            )
            ui.label(
                "Edit any value below and click \"Save & Next\" -- only boxes you actually "
                "change get saved. Use Skip if nothing needs correcting for this student."
            ).classes("text-xs text-gray-500")

            for sem in semesters_present:
                sem_records = [r for r in records if r["semester_label"] == sem]
                ui.separator().classes("my-2")
                ui.label(sem.title()).classes("text-md font-bold text-primary mt-2")

                identity = {
                    r["group_name"]: r["value"] for r in sem_records
                    if r["group_name"] in mt.IDENTITY_GROUPS
                }
                identity_text = "   ".join(
                    f"{mt.IDENTITY_GROUP_LABELS.get(g, g.title())}: {identity[g]}"
                    for g in mt.IDENTITY_GROUPS if identity.get(g)
                )
                if identity_text:
                    ui.label(identity_text).classes("text-xs italic text-gray-600 mb-1")

                marks_records = sorted(
                    [r for r in sem_records if r["group_name"] == "obtained_marks"],
                    key=lambda r: (r["abs_row"], r["abs_col"]),
                )
                if marks_records:
                    with ui.grid(columns=3).classes("gap-x-3 gap-y-1 items-center mt-1"):
                        ui.label("Subject").classes("text-xs font-bold")
                        ui.label("Component").classes("text-xs font-bold")
                        ui.label("Marks").classes("text-xs font-bold")
                        for r in marks_records:
                            subject_name = subject_name_by_sem_row.get(
                                (sem, r["abs_row"]), f"Row {r['abs_row']}"
                            )
                            component = component_by_sem_col.get(
                                (sem, r["abs_col"]), f"Col {r['abs_col']}"
                            )
                            key = (sem, "obtained_marks", r["abs_row"], r["abs_col"])
                            ui.label(subject_name).classes("text-xs")
                            ui.label(component).classes("text-xs")
                            ui.input(
                                value=values.get(key, ""),
                                on_change=lambda e, k=key: on_value_change(e, k),
                            ).props("dense outlined").classes("w-24")

                # Subject/level/leaf marks for semesters trained through the
                # newer tree trainer -- lives in subjectwise_student_records,
                # not student_records, so it's a separate block from the
                # flat marks_records grid above (see on_sw_value_change).
                sw_keys_this_sem = [k for k in sw_meta if k[0] == sem]
                if sw_keys_this_sem:
                    by_subject = {}
                    for key in sw_keys_this_sem:
                        _, subject_index, node_id, role = key
                        subj_name = sw_meta[key]["subject_name"]
                        by_subject.setdefault((subject_index, subj_name), {}).setdefault(
                            node_id, {}
                        )[role] = key

                    for (subject_index, subj_name), leaves in sorted(by_subject.items()):
                        ui.label(subj_name).classes("text-xs font-bold mt-2")
                        with ui.grid(columns=4).classes("gap-x-3 gap-y-1 items-center mt-1"):
                            ui.label("Level / Leaf").classes("text-xs font-bold")
                            ui.label("Max").classes("text-xs font-bold")
                            ui.label("Obtained").classes("text-xs font-bold")
                            ui.label("").classes("text-xs font-bold")
                            for node_id, roles in sorted(
                                leaves.items(), key=lambda kv: kv[0]
                            ):
                                any_key = next(iter(roles.values()))
                                label = sw_meta[any_key]["component_label"]
                                ui.label(label).classes("text-xs")
                                max_key = roles.get("max")
                                obt_key = roles.get("obtained")
                                if max_key:
                                    ui.input(
                                        value=sw_values.get(max_key, ""),
                                        on_change=lambda e, k=max_key: on_sw_value_change(e, k),
                                    ).props("dense outlined").classes("w-20")
                                else:
                                    ui.label("--").classes("text-xs")
                                if obt_key:
                                    ui.input(
                                        value=sw_values.get(obt_key, ""),
                                        on_change=lambda e, k=obt_key: on_sw_value_change(e, k),
                                    ).props("dense outlined").classes("w-20")
                                else:
                                    ui.label("--").classes("text-xs")
                                ui.label("")

                summary_records = {
                    r["group_name"]: r for r in sem_records if r["group_name"] in mt.SUMMARY_GROUPS
                }
                if summary_records:
                    with ui.row().classes("gap-4 mt-2 flex-wrap items-center"):
                        for g in mt.SUMMARY_GROUPS:
                            r = summary_records.get(g)
                            if not r:
                                continue
                            key = (sem, g, r["abs_row"], r["abs_col"])
                            ui.label(mt.SUMMARY_GROUP_LABELS.get(g, g.title()) + ":").classes(
                                "text-xs font-semibold"
                            )
                            ui.input(
                                value=values.get(key, ""),
                                on_change=lambda e, k=key: on_value_change(e, k),
                            ).props("dense outlined").classes("w-28")

            with ui.row().classes("gap-2 mt-4"):
                ui.button(
                    "Save & Next", icon="save", on_click=recheck_queue_manual_save_and_next,
                ).props("unelevated color=primary")
                ui.button("Skip", icon="skip_next", on_click=recheck_queue_manual_skip).props("outline")
                if state["recheck_queue_pos"] > 0:
                    ui.button("Back", icon="arrow_back", on_click=recheck_queue_back).props("outline")
                ui.button("Cancel Queue", icon="close", on_click=reset_recheck_to_choose).props(
                    "outline color=negative"
                )


def render_recheck_queue_delete_editor(container):
    enrollment = state["recheck_manual_enrollment"]
    semesters_present = state["recheck_delete_semesters_present"]
    delete_semesters = state["recheck_manual_delete_semesters"]

    def on_delete_toggle(e, sem):
        if e.value:
            delete_semesters.add(sem)
        else:
            delete_semesters.discard(sem)

    with container:
        with ui.card().classes("w-full border-2 border-red-200"):
            render_recheck_queue_progress("delete")
            ui.label(f"Delete Data -- Enrollment {enrollment}").classes(
                "text-lg font-semibold text-red-700 mt-1"
            )
            ui.label(
                "Tick the semester(s) whose result record you want permanently removed "
                "from the database, then \"Delete Selected & Next\". Ticked semesters are "
                "deleted only -- untouched semesters stay exactly as they are. Use Skip if "
                "nothing needs deleting for this student. This never touches Seating Chart "
                "data."
            ).classes("text-xs text-gray-500")
            with ui.row().classes("gap-4 mt-3 flex-wrap"):
                for sem in semesters_present:
                    ui.checkbox(
                        sem.title(), value=sem in delete_semesters,
                        on_change=lambda e, s=sem: on_delete_toggle(e, s),
                    )
            with ui.row().classes("gap-2 mt-4"):
                ui.button(
                    "Delete Selected & Next", icon="delete_forever",
                    on_click=recheck_queue_delete_confirm_and_next,
                ).props("unelevated color=negative")
                ui.button("Skip", icon="skip_next", on_click=recheck_queue_delete_skip).props("outline")
                if state["recheck_queue_pos"] > 0:
                    ui.button("Back", icon="arrow_back", on_click=recheck_queue_back).props("outline")
                ui.button("Cancel Queue", icon="close", on_click=reset_recheck_to_choose).props("outline")


def render_recheck_queue_manual_done(container):
    _render_recheck_queue_summary(container, "manual")


def render_recheck_queue_delete_done(container):
    _render_recheck_queue_summary(container, "delete")


def _render_recheck_queue_summary(container, mode):
    stats = state["recheck_queue_stats"]
    log = state["recheck_queue_log"]
    title = "Manual Recheck complete!" if mode == "manual" else "Delete complete!"
    primary_label = "Saved" if mode == "manual" else "Deleted"
    primary_key = "saved" if mode == "manual" else "deleted"
    start_again = start_manual_recheck_queue if mode == "manual" else start_delete_recheck_queue

    with container:
        with ui.card().classes("w-full"):
            ui.label(title).classes("text-xl font-bold text-green-700")
            with ui.grid(columns=2).classes("gap-x-6 gap-y-1 mt-3 text-sm"):
                ui.label("Enrollment numbers in list:")
                ui.label(str(len(state["recheck_queue_list"]))).classes("font-semibold")
                ui.label(f"{primary_label}:")
                ui.label(str(stats.get(primary_key, 0))).classes("font-semibold text-green-700")
                ui.label("Skipped:")
                ui.label(str(stats.get("skipped", 0))).classes("font-semibold")
                ui.label("Not found in database:")
                ui.label(str(stats.get("not_found", 0))).classes(
                    "font-semibold" + (" text-orange-600" if stats.get("not_found") else "")
                )

            if log:
                with ui.expansion("Log", icon="article").classes("w-full text-xs mt-3"):
                    with ui.column().classes("gap-0.5"):
                        for entry in log:
                            color = {
                                "saved": "text-green-700", "deleted": "text-red-700",
                                "skipped": "text-gray-600", "not_found": "text-orange-600",
                            }.get(entry["status"], "text-gray-600")
                            ui.label(
                                f"{entry['enrollment']}: {entry['status']} -- {entry['detail']}"
                            ).classes(f"text-xs font-mono {color}")

            with ui.row().classes("gap-2 mt-4"):
                ui.button(
                    "Run Again on Same List", icon="replay", on_click=start_again,
                ).props("outline")
                ui.button(
                    "Back to Recheck", icon="arrow_back", on_click=reset_recheck_to_choose,
                ).props("outline")
                ui.button(
                    "Mark Complete", icon="check_circle",
                    on_click=lambda: mark_complete_and_advance("recheck"),
                ).props("unelevated color=positive")


# =======================================================================
# TOP AREA + MODE CONTENT DISPATCH
# =======================================================================

def render_top_area():
    try:
        top_container.clear()
    except RuntimeError:
        # See render_mode_content(): stale client from a page reload that
        # happened mid-background-task. Nothing left to render into.
        return
    mode = state["mode"]
    if mode in MODE_ORDER + ["report"] and not state["scheme_group_called"]:
        return  # render_mode_content()'s "No scheme selected" wall covers this; no input box either
    with top_container:
        if mode == "train":
            step = state["train_step"]
            if step == "input":
                with ui.card().classes("w-full"):
                    ui.label("Sample Enrollment Numbers").classes("text-md font-semibold")
                    ui.label(
                        "One enrollment number per line, any count -- paste directly from "
                        "Seating Chart's \"Recommended Enrollment Numbers for Train Mode\" "
                        "list for this scheme, or type/paste your own."
                    ).classes("text-xs text-gray-500")
                    ui.textarea(
                        placeholder="e.g.\n2100120001\n2100120002",
                        value=state["train_enrollments_text"],
                        on_change=lambda e: (
                            state.update(train_enrollments_text=e.value),
                            render_mode_content(),
                        ),
                    ).classes("w-full mt-2").props("outlined rows=6")
                    ui.button(
                        "Fetch These", icon="cloud_download", on_click=start_train_fetch,
                    ).classes("mt-3").props("unelevated color=primary")
            elif step == "fetching":
                with ui.card().classes("w-full"):
                    ui.label("Fetching in progress -- solve captchas as they appear below.").classes(
                        "text-sm"
                    )
            elif step in ("select_ranges", "subjectwise_panel", "wizard_done"):
                idx = state["train_current_idx"]
                total = len(state["train_order"])
                label = state["train_order"][idx]
                with ui.card().classes("w-full"):
                    ui.label(f"Training: semester {idx + 1} of {total} -- {label}").classes(
                        "text-sm font-semibold"
                    )
            elif step == "done":
                with ui.card().classes("w-full"):
                    ui.label("Training complete.").classes("text-sm font-semibold text-green-700")
        elif mode == "extract" or (
            mode == "recheck"
            and state["recheck_step"] in ("choose", "automatic_running", "automatic_done")
        ):
            with ui.card().classes("w-full"):
                ui.label("Enrollment Numbers").classes("text-md font-semibold")
                ui.label(
                    "Paste enrollment numbers, one per line. Used by Extract and all three "
                    "Recheck actions (Automatic, Manual, Delete)."
                ).classes("text-xs text-gray-500")
                ui.textarea(
                    placeholder="e.g.\n2100120001\n2100120002\n2100120003",
                    value=state["enrollment_text"],
                    on_change=lambda e: (
                        state.update(enrollment_text=e.value),
                        render_mode_content(),
                    ),
                ).classes("w-full").props("outlined rows=6")
        # report / coursecodes: no shared top area needed -- neither
        # mode touches enrollment numbers.


SCROLL_TRACKED_IDS = ["trainer-sidebar-scroll", "trainer-grid-scroll", "ptt-matrix-scroll"]


def restore_scroll_positions():
    """Puts each tracked container's scrollTop back where it was before
    this render, using the page-level JS map that survived the DOM
    rebuild (see the scroll listener injected in main_page()). Safe to
    call even when a given id isn't present in the current step's DOM --
    getElementById just returns null and the line is skipped.

    Retried a few times over the next ~300ms rather than just once: right
    after a render, the new DOM may not have finished layout yet (the
    container's scrollHeight can still be 0), so setting scrollTop
    immediately can silently no-op. A few staggered retries make this
    reliable without needing a MutationObserver."""
    ids_js = json.dumps(SCROLL_TRACKED_IDS)
    js = f"""
        (function() {{
            var ids = {ids_js};
            function apply() {{
                ids.forEach(function(cid) {{
                    var el = document.getElementById(cid);
                    if (el && window.__scrollPos && window.__scrollPos[cid] != null) {{
                        el.scrollTop = window.__scrollPos[cid];
                    }}
                }});
            }}
            [0, 40, 120, 300].forEach(function(delay) {{ setTimeout(apply, delay); }});
        }})();
    """
    try:
        ui.run_javascript(js)
    except RuntimeError:
        # The client/page this task was rendering into is gone (browser
        # reloaded/reconnected while a background op -- e.g. train fetch --
        # was still running). Nothing to restore scroll into; ignore.
        pass


def _offline_reset_draft():
    state["offline_draft_name"] = ""
    state["offline_draft_levels"] = 2
    state["offline_draft_leaf_count"] = 1
    _offline_resize_draft_grid()


def _offline_resize_draft_grid():
    """Pads/truncates the draft's level-label grid and max-value row to
    match the currently chosen levels/leaf_count, keeping whatever the
    user already typed wherever the shape still lines up."""
    levels = max(1, int(state["offline_draft_levels"] or 1))
    leaf_count = max(1, int(state["offline_draft_leaf_count"] or 1))
    old_labels = state["offline_draft_level_labels"]
    new_labels = []
    for lvl in range(levels):
        old_row = old_labels[lvl] if lvl < len(old_labels) else []
        new_labels.append([(old_row[i] if i < len(old_row) else "") for i in range(leaf_count)])
    state["offline_draft_level_labels"] = new_labels
    old_max = state["offline_draft_max_values"]
    state["offline_draft_max_values"] = [(old_max[i] if i < len(old_max) else "") for i in range(leaf_count)]


def _offline_split_pasted(raw, leaf_count):
    """If raw looks like a paste of multiple values (comma- or tab-
    separated -- Excel row-copies use tabs, typed lists use commas)
    rather than a single typed value, split it into up to leaf_count
    parts (blank-padded/truncated to fit). Returns None for an ordinary
    single value, so normal typing in any one box still behaves as a
    plain single-cell edit."""
    text = (raw or "").strip()
    if not text:
        return None
    sep = "\t" if "\t" in text else ("," if "," in text else None)
    if sep is None:
        return None
    parts = [p.strip() for p in text.split(sep)]
    if len(parts) < 2:
        return None
    parts = (parts + [""] * leaf_count)[:leaf_count]
    return parts


def _offline_split_pasted_multi(raw, count):
    """Like _offline_split_pasted, but also recognizes an Excel COLUMN
    copy (one cell per line, newline-separated) in addition to a ROW
    copy (tab-separated) or a typed comma list -- used for the
    Name/Levels/Leaf-Columns setup table, where pasting down a column
    is the natural motion."""
    text = (raw or "").strip()
    if not text:
        return None
    if "\n" in text:
        parts = [p.strip() for p in text.replace("\r\n", "\n").replace("\r", "\n").split("\n") if p.strip() != ""]
    elif "\t" in text:
        parts = [p.strip() for p in text.split("\t")]
    elif "," in text:
        parts = [p.strip() for p in text.split(",")]
    else:
        return None
    if len(parts) < 2:
        return None
    parts = (parts + [""] * count)[:count]
    return parts


def _offline_resize_subject_grid(subj):
    """Pads/truncates one subject's level-label grid and max-value row to
    match the GLOBAL levels count and this subject's own leaf_count,
    keeping whatever was already typed wherever the shape still lines
    up. Levels is global/uniform across every subject (confirmed) --
    only leaf_count varies per subject."""
    levels = max(1, int(state["offline_levels"] or 1))
    leaf_count = max(1, int(subj.get("leaf_count") or 1))
    old_labels = subj.get("level_labels") or []
    new_labels = []
    for lvl in range(levels):
        old_row = old_labels[lvl] if lvl < len(old_labels) else []
        new_labels.append([(old_row[i] if i < len(old_row) else "") for i in range(leaf_count)])
    subj["level_labels"] = new_labels
    old_max = subj.get("max_values") or []
    subj["max_values"] = [(old_max[i] if i < len(old_max) else "") for i in range(leaf_count)]


def _offline_resize_subject_count(count):
    """Grows/shrinks state['offline_subjects'] to exactly `count`
    entries, preserving existing ones (so changing the count doesn't
    wipe out what's already been typed)."""
    count = max(1, int(count or 1))
    subs = state["offline_subjects"]
    while len(subs) < count:
        subs.append({"name": "", "leaf_count": 1, "level_labels": [], "max_values": []})
    del subs[count:]
    for s in subs:
        _offline_resize_subject_grid(s)


def _offline_assign_flat_row(subjects, values, level_idx=None):
    """Distributes one flat, whole-row pasted list of values back across
    every subject's own slice of that row, in subject order -- subject 1
    gets the first leaf_count values, subject 2 gets the next
    leaf_count values, and so on, with nothing skipped since every
    subject participates in every row (levels are uniform, so this is
    always a clean rectangle, never a partial row).

    level_idx=None means this is the Max row; otherwise it's Level
    `level_idx` (0-based).
    """
    idx = 0
    for subj in subjects:
        n = len(subj["max_values"])
        chunk = values[idx:idx + n]
        idx += n
        if level_idx is None:
            subj["max_values"] = chunk
        else:
            subj["level_labels"][level_idx] = chunk


def render_offline_setup(container):
    settings = mt.load_report_settings(mt.DB_FILE)
    with container:
        with ui.card().classes("w-full"):
            ui.label("Offline Import").classes("text-xl font-bold")
            ui.label(MODE_DESCRIPTIONS["offline"]).classes("text-sm text-gray-600")

        with ui.card().classes("w-full mt-3"):
            ui.label("Common Fields").classes("text-md font-semibold")
            ui.label(
                "Institute Name, Institute Address, Year, and Program are GLOBAL -- typed "
                "once, saved here, and stay filled in for every future semester you import "
                "(including after clicking \"Import Another Semester\"). Only Semester "
                "(and subjects) change per import."
            ).classes("text-xs text-gray-500")
            with ui.row().classes("gap-3 mt-2"):
                name_input = ui.input(
                    label="Institute Name", value=settings.get("institute_name", ""),
                ).classes("w-72").props("outlined dense")
                address_input = ui.input(
                    label="Institute Address", value=settings.get("institute_address", ""),
                ).classes("w-96").props("outlined dense")

            with ui.row().classes("gap-3 mt-3"):
                year_input = ui.input(
                    label="Year", value=state["offline_year"] or settings.get("year", ""),
                    placeholder="e.g. Summer 2026",
                    on_change=lambda e: state.update(offline_year=e.value),
                ).classes("w-48").props("outlined dense")
                program_input = ui.input(
                    label="Program", value=state["offline_program"] or settings.get("program", ""),
                    on_change=lambda e: state.update(offline_program=e.value),
                ).classes("w-64").props("outlined dense")
                ui.select(
                    options=mt.SEMESTER_NAMES, value=state["offline_semester"] or None,
                    with_input=True, new_value_mode="add-unique",
                    label="Semester",
                    on_change=lambda e: state.update(offline_semester=e.value),
                ).classes("w-64").props("outlined dense")
            ui.label(
                "Year format: session + full year, e.g. \"Summer 2026\" or \"Winter 2025\" -- "
                "not \"2025-2026\" (that range is derived automatically for the report header)."
            ).classes("text-xs text-gray-500 mt-1")

            def save_common_fields():
                state["offline_year"] = year_input.value
                state["offline_program"] = program_input.value
                mt.save_report_settings(
                    {
                        "institute_name": name_input.value, "institute_address": address_input.value,
                        "year": year_input.value, "program": program_input.value,
                    },
                    mt.DB_FILE,
                )
                ui.notify("Common fields saved.", type="positive")

            ui.button("Save Common Fields", icon="save", on_click=save_common_fields).classes("mt-3").props(
                "outlined dense"
            )

        if not state["offline_setup_locked"]:
            _render_offline_subject_count_step(container)
        else:
            _render_offline_combined_grid_step(container)


def _render_offline_subject_count_step(container):
    with container:
        with ui.card().classes("w-full mt-3"):
            ui.label("2. How many subjects, and how many levels?").classes("text-md font-semibold")
            ui.label(
                "Levels is GLOBAL -- the same for every subject (e.g. Theory -> FA/SA is "
                "2 levels for everyone). Only the number of leaf columns (final Max/"
                "Obtained columns) varies per subject."
            ).classes("text-xs text-gray-500")

            with ui.row().classes("gap-3 mt-2 items-end"):
                def on_count_blur():
                    _offline_resize_subject_count(state["offline_subject_count"])
                    render_mode_content()

                ui.number(
                    label="Number of Subjects", value=state["offline_subject_count"], min=1, max=30,
                    on_change=lambda e: state.update(offline_subject_count=e.value),
                ).classes("w-48").props("outlined dense").on("blur", on_count_blur)

                def on_levels_blur():
                    for s in state["offline_subjects"]:
                        _offline_resize_subject_grid(s)
                    render_mode_content()

                ui.number(
                    label="Levels (global)", value=state["offline_levels"], min=1, max=6,
                    on_change=lambda e: state.update(offline_levels=e.value),
                ).classes("w-40").props("outlined dense").on("blur", on_levels_blur)

        if state["offline_subjects"]:
            with ui.card().classes("w-full mt-3"):
                ui.label("3. Name / Leaf Columns -- one row per subject").classes(
                    "text-md font-semibold"
                )
                ui.label(
                    "Tip: paste a whole list into the FIRST box of a column (Name or Leaf "
                    "Columns) to fill it down for every subject at once -- works with a "
                    "copied Excel column, a copied Excel row, or a typed comma list."
                ).classes("text-xs text-blue-600")

                n = len(state["offline_subjects"])
                with ui.column().classes("gap-1 mt-2 w-full"):
                    with ui.row().classes("gap-2 font-semibold text-xs text-gray-600"):
                        ui.label("#").classes("w-6")
                        ui.label("Subject Name").classes("w-64")
                        ui.label("Leaf Columns").classes("w-32")

                    for i, subj in enumerate(state["offline_subjects"]):
                        with ui.row().classes("gap-2 items-center"):
                            ui.label(str(i + 1)).classes("w-6 text-xs text-gray-500")

                            def on_name_input(e, i=i):
                                state["offline_subjects"][i]["_name_raw"] = e.value

                            def on_name_blur(i=i):
                                raw = state["offline_subjects"][i].pop("_name_raw", None)
                                if i == 0:
                                    parts = _offline_split_pasted_multi(raw, n)
                                    if parts is not None:
                                        for j, val in enumerate(parts):
                                            state["offline_subjects"][j]["name"] = val
                                        render_mode_content()
                                        return
                                if raw is not None:
                                    state["offline_subjects"][i]["name"] = raw
                                    render_mode_content()

                            ui.input(
                                value=subj["name"], placeholder="Subject name",
                                on_change=on_name_input,
                            ).classes("w-64").props("outlined dense").on("blur", lambda e, i=i: on_name_blur(i))

                            def on_leaf_input(e, i=i):
                                state["offline_subjects"][i]["_leaf_raw"] = e.value

                            def on_leaf_blur(i=i):
                                raw = state["offline_subjects"][i].pop("_leaf_raw", None)
                                if i == 0:
                                    parts = _offline_split_pasted_multi(raw, n)
                                    if parts is not None:
                                        for j, val in enumerate(parts):
                                            try:
                                                state["offline_subjects"][j]["leaf_count"] = max(1, int(float(val)))
                                            except (ValueError, TypeError):
                                                pass
                                        render_mode_content()
                                        return
                                if raw is not None:
                                    try:
                                        state["offline_subjects"][i]["leaf_count"] = max(1, int(float(raw)))
                                    except (ValueError, TypeError):
                                        pass
                                    render_mode_content()

                            ui.input(
                                value=str(subj["leaf_count"]), placeholder="e.g. 6",
                                on_change=on_leaf_input,
                            ).classes("w-32").props("outlined dense").on("blur", lambda e, i=i: on_leaf_blur(i))

                def build_grid():
                    if any(not (s["name"] or "").strip() for s in state["offline_subjects"]):
                        ui.notify("Every subject needs a name.", type="warning")
                        return
                    for s in state["offline_subjects"]:
                        _offline_resize_subject_grid(s)
                    state["offline_setup_locked"] = True
                    render_mode_content()

                ui.button(
                    "Build Grid for All Subjects", icon="grid_on", on_click=build_grid,
                ).classes("mt-3").props("unelevated color=primary")


def _render_offline_combined_grid_step(container):
    subjects = state["offline_subjects"]
    total_leaves = sum(len(s["max_values"]) for s in subjects)
    levels = len(subjects[0]["level_labels"]) if subjects else 0

    with container:
        with ui.card().classes("w-full mt-3"):
            with ui.row().classes("items-center justify-between w-full"):
                ui.label("3. Fill in Level labels and Max marks -- one row per level, spanning every subject").classes(
                    "text-md font-semibold"
                )
                ui.button(
                    "Edit Subject Count / Names", icon="arrow_back",
                    on_click=lambda: (state.update(offline_setup_locked=False), render_mode_content()),
                ).props("flat dense")
            ui.label(
                "Tip: paste ONE list into the very first box of a row to fill that whole "
                "row across EVERY subject at once, left to right in the same order as your "
                f"subject table ({total_leaves} leaf columns total, {levels} level row(s))."
            ).classes("text-xs text-blue-600")

            # Subject-name header, spanning each subject's own leaf-column
            # width, so it's visually clear which boxes below belong to
            # which subject even though the boxes themselves are one
            # continuous row.
            with ui.row().classes("gap-2 mt-3"):
                ui.label("").classes("w-20")
                for subj in subjects:
                    leaf_count = len(subj["max_values"])
                    width_px = leaf_count * 120 - 8
                    ui.label(f"{subj['name']} ({leaf_count})").classes(
                        "text-xs font-bold text-gray-700 text-center"
                    ).style(f"width:{width_px}px")

            for lvl in range(levels):
                with ui.row().classes("gap-2 mt-1"):
                    ui.label(f"Level {lvl + 1}").classes("w-20 text-xs text-gray-600 mt-3")
                    box_i = 0
                    for subj in subjects:
                        leaf_count = len(subj["max_values"])
                        for leaf_i in range(leaf_count):
                            def on_label_change(e, box_i=box_i, lvl=lvl):
                                if box_i == 0:
                                    parts = _offline_split_pasted(e.value, total_leaves)
                                    if parts is not None:
                                        _offline_assign_flat_row(subjects, parts, level_idx=lvl)
                                        render_mode_content()
                                        return
                                # Not a whole-row paste -- just this one cell.
                                idx = 0
                                for s in subjects:
                                    n = len(s["max_values"])
                                    if box_i < idx + n:
                                        s["level_labels"][lvl][box_i - idx] = e.value
                                        return
                                    idx += n

                            ui.input(
                                value=subj["level_labels"][lvl][leaf_i], placeholder=f"Leaf {leaf_i + 1}",
                                on_change=on_label_change,
                            ).classes("w-28").props("outlined dense")
                            box_i += 1

            with ui.row().classes("gap-2 mt-1"):
                ui.label("Max").classes("w-20 text-xs text-gray-600 mt-3")
                box_i = 0
                for subj in subjects:
                    leaf_count = len(subj["max_values"])
                    for leaf_i in range(leaf_count):
                        def on_max_change(e, box_i=box_i):
                            if box_i == 0:
                                parts = _offline_split_pasted(e.value, total_leaves)
                                if parts is not None:
                                    _offline_assign_flat_row(subjects, parts, level_idx=None)
                                    render_mode_content()
                                    return
                            idx = 0
                            for s in subjects:
                                n = len(s["max_values"])
                                if box_i < idx + n:
                                    s["max_values"][box_i - idx] = e.value
                                    return
                                idx += n

                        ui.input(
                            value=subj["max_values"][leaf_i], placeholder=f"Leaf {leaf_i + 1}",
                            on_change=on_max_change,
                        ).classes("w-28").props("outlined dense")
                        box_i += 1

        with ui.card().classes("w-full mt-3"):
            def save_structure():
                semester = (state["offline_semester"] or "").strip()
                if not semester:
                    ui.notify("Choose a semester first.", type="warning")
                    return
                if not (state["offline_year"] or "").strip():
                    ui.notify("Enter the Year first.", type="warning")
                    return
                if not (state["offline_program"] or "").strip():
                    ui.notify("Enter the Program first.", type="warning")
                    return
                subjects = state["offline_subjects"]
                if any(not (v or "").strip() for s in subjects for row in s["level_labels"] for v in row):
                    ui.notify("Fill in every level-label cell before saving.", type="warning")
                    return
                if any(not (v or "").strip() for s in subjects for v in s["max_values"]):
                    ui.notify("Fill in every Max marks cell before saving.", type="warning")
                    return
                template = mt.build_offline_template(subjects)
                mt.save_offline_structure_to_db(semester, template, mt.DB_FILE)
                state["offline_template"] = template
                state["offline_parsed_rows"] = None
                state["offline_paste_text"] = ""
                state["offline_step"] = "paste"
                render_mode_content()
                ui.notify(f"Structure saved for {semester}.", type="positive")

            ui.button(
                "Save Structure & Continue to Data Entry", icon="check", on_click=save_structure,
            ).props("unelevated color=primary")


def render_offline_paste(container):
    semester = state["offline_semester"]
    year = state["offline_year"]
    program = state["offline_program"]
    template = state["offline_template"]
    leaf_columns = template["leaf_columns"]
    identity_labels = [g.replace("_", " ").title() for g in mt.OFFLINE_ROW_GROUPS]
    column_labels = identity_labels + [f"{c['subject_name']} / {c['component_label']}" for c in leaf_columns]

    with container:
        with ui.card().classes("w-full"):
            ui.label(f"Offline Import -- {semester}").classes("text-xl font-bold")
            ui.label(f"Year: {year or '(not set)'}   |   Program: {program or '(not set)'}").classes(
                "text-xs text-gray-500"
            )
            ui.label(
                "Paste one row per student, copied straight from your Excel sheet. "
                "Columns must be in this exact order (tab-separated, i.e. a normal "
                "Excel copy) -- Year/Program/Semester are NOT pasted columns, they're "
                "the common fields set above."
            ).classes("text-sm text-gray-600")
            ui.label(" | ".join(column_labels)).classes("text-xs text-gray-500 mt-1 italic")

            header_row_tsv = "\t".join(column_labels)

            def copy_header_row():
                ui.run_javascript(f"navigator.clipboard.writeText({json.dumps(header_row_tsv)})")
                ui.notify(
                    "Header row copied -- paste it into row 1 of a blank Excel sheet, "
                    "fill in student data below it, then copy just the data rows back here.",
                    type="positive",
                )

            ui.button("Copy Header Row for Excel", icon="content_copy", on_click=copy_header_row).classes(
                "mt-2"
            ).props("outlined dense")
            ui.label(
                "Tip: this copies the column headers above as one tab-separated row, ready "
                "to paste directly into row 1 of Excel -- so your sheet's columns line up "
                "exactly, with no retyping and no chance of a mismatched column."
            ).classes("text-xs text-gray-500 mt-1")

            ui.button(
                "Edit Structure Instead", icon="arrow_back",
                on_click=lambda: (state.update(offline_step="setup"), render_mode_content()),
            ).props("flat dense").classes("mt-2")

        with ui.card().classes("w-full mt-3"):
            ui.label("Paste student data").classes("text-md font-semibold")
            ui.textarea(
                placeholder="Paste the whole block here (Ctrl+V straight from Excel)...",
                value=state["offline_paste_text"],
                on_change=lambda e: state.update(offline_paste_text=e.value),
            ).classes("w-full").props("outlined rows=10")

            def parse_rows():
                text = state["offline_paste_text"]
                if not (text or "").strip():
                    ui.notify("Paste some rows first.", type="warning")
                    return
                rows = mt.parse_pasted_grid(text)
                expected_len = len(mt.OFFLINE_ROW_GROUPS) + len(leaf_columns)
                errors = [
                    f"Row {i + 1}: expected {expected_len} columns, found {len(r)}"
                    for i, r in enumerate(rows) if len(r) != expected_len
                ]
                state["offline_parsed_rows"] = rows
                state["offline_parse_errors"] = errors
                render_mode_content()

            ui.button("Parse", icon="playlist_add_check", on_click=parse_rows).classes("mt-2").props(
                "unelevated color=primary"
            )

        rows = state["offline_parsed_rows"]
        if rows is not None:
            with ui.card().classes("w-full mt-3"):
                ui.label(f"Preview -- {len(rows)} row(s) parsed").classes("text-md font-semibold")
                if state["offline_parse_errors"]:
                    with ui.column().classes("gap-0 mt-1"):
                        ui.label("Column-count problems (fix in your paste and re-Parse):").classes(
                            "text-xs text-red-600 font-semibold"
                        )
                        for err in state["offline_parse_errors"][:20]:
                            ui.label(f"- {err}").classes("text-xs text-red-600")

                preview_rows = rows[:20]
                columns = [{"name": f"c{i}", "label": lbl, "field": f"c{i}"} for i, lbl in enumerate(column_labels)]
                table_rows = [
                    {f"c{i}": (r[i] if i < len(r) else "") for i in range(len(column_labels))}
                    for r in preview_rows
                ]
                ui.table(columns=columns, rows=table_rows).classes("w-full mt-2").props("dense")
                if len(rows) > 20:
                    ui.label(f"...showing first 20 of {len(rows)} rows.").classes("text-xs text-gray-500 mt-1")

                def save_data():
                    saved, errors = mt.save_offline_student_rows(
                        semester, year, program, leaf_columns, state["offline_parsed_rows"], mt.DB_FILE
                    )
                    state["offline_saved_count"] = saved
                    state["offline_save_errors"] = errors
                    state["offline_step"] = "done"
                    state["completed"].add("offline")
                    render_mode_content()

                ui.button("Save to Database", icon="save", on_click=save_data).classes("mt-3").props(
                    "unelevated color=primary"
                )


def render_offline_done(container):
    with container:
        with ui.card().classes("w-full"):
            ui.label("Offline Import Complete").classes("text-xl font-bold text-green-700")
            ui.label(
                f"Saved {state['offline_saved_count']} student row(s) for {state['offline_semester']}."
            ).classes("text-sm")
            if state["offline_save_errors"]:
                ui.label("Some rows were skipped:").classes("text-xs text-red-600 font-semibold mt-2")
                for err in state["offline_save_errors"][:20]:
                    ui.label(f"- {err}").classes("text-xs text-red-600")

            def start_new():
                state["offline_step"] = "setup"
                state["offline_semester"] = ""
                # Institute Name/Address/Year/Program are GLOBAL -- intentionally
                # left untouched here so the next semester's import starts with
                # them already filled in (loaded fresh from report_settings on
                # the next render anyway).
                state["offline_subject_count"] = 1
                state["offline_setup_locked"] = False
                state["offline_subjects"] = []
                state["offline_template"] = None
                state["offline_paste_text"] = ""
                state["offline_parsed_rows"] = None
                state["offline_parse_errors"] = []
                render_mode_content()

            with ui.row().classes("gap-2 mt-3"):
                ui.button("Import Another Semester", icon="add", on_click=start_new).props(
                    "unelevated color=primary"
                )
                ui.button(
                    "Go to Report Mode", icon="picture_as_pdf",
                    on_click=lambda: select_mode("report"),
                ).props("outlined")


def confirm_delete_sitting(year, session):
    """Deletes ONE sitting's seating chart data (file + scheme declarations) after
    confirmation, then refreshes the sidebar so a deleted sitting's Active Scheme
    list / buttons disappear immediately."""
    def do_wipe():
        dialog.close()
        dept = state["logged_in"]
        count = mt.wipe_seating_chart_data(dept["institute_name"], dept["department_name"], year, session)
        deleted_year_s = mt.sanitize_path_component(year)
        deleted_session_s = mt.sanitize_path_component(session).lower()

        act = state["active_scheme"]
        if act and act["year"] == deleted_year_s and act["session"] == deleted_session_s:
            global REPORTS_DIR
            state["active_scheme"] = None
            state["scheme_group_called"] = False
            # Point the shared module-level paths back at neutral defaults (same as
            # logout) so nothing keeps referring to the deleted scheme's files.
            mt.set_active_scheme_db("msbte_data.db")
            mt.set_active_department_mapping_file("layout_mapping.json")
            REPORTS_DIR = "reports"
            mt.set_active_department_context("", "", "", "", "")
            reset_all_operational_modes()

        for ykey, skey in (("seating_paste_year", "seating_paste_session"),
                           ("seating_manual_year", "seating_manual_session")):
            if (mt.sanitize_path_component(state[ykey]) == deleted_year_s
                    and mt.sanitize_path_component(state[skey]).lower() == deleted_session_s):
                state[ykey] = ""
        state["seating_columns"] = {k: "" for k, _ in SEATING_COLUMN_SPECS}
        state["seating_parsed_rows"] = None
        state["seating_parse_errors"] = []
        state["seating_last_saved_count"] = None
        state["seating_last_save_errors"] = []
        state["seating_manual_last_confirmed"] = None
        ui.notify(f"Deleted {year} / {session} ({count} seating chart row(s)).", type="positive")
        render_mode_content()
        refresh_scheme_sidebar()
        update_mode_buttons()

    with ui.dialog() as dialog, ui.card():
        ui.label(f"Delete seating chart data for {year} / {session}?").classes("text-md font-bold text-red-700")
        ui.label(
            "This permanently deletes EVERYTHING for THIS year/session: the seating chart, "
            "its scheme list, and every scheme database (K.db, I.db, ...) with all Train / "
            "Extract / Course Codes / Offline Import / Recheck data and layout mappings "
            "inside it. Other years/sessions are unaffected. Generated report PDFs are "
            "kept. This cannot be undone."
        ).classes("text-sm mt-1")
        with ui.row().classes("gap-2 mt-4"):
            ui.button("Delete", icon="delete_forever", on_click=do_wipe).props("unelevated color=negative")
            ui.button("Cancel", on_click=dialog.close).props("outline")
    dialog.open()


def confirm_wipe_seating_chart():
    """Top-right 'Delete All Seating Chart Data' button -- deletes the sitting
    currently typed/selected in Year/Session."""
    if state["seating_manual_mode"]:
        year, session = state["seating_manual_year"], state["seating_manual_session"]
    else:
        year, session = state["seating_paste_year"], state["seating_paste_session"]
    if not (year or "").strip():
        ui.notify("Select or enter a Year/Session first.", type="warning")
        return
    confirm_delete_sitting(year, session)


def reset_all_operational_modes():
    """Returns every one of Train/Extract/Course Codes/Recheck/Offline
    Import/Report's own UI state to its true starting value -- same
    values the initial `state` dict above defines. This is what "Call
    Global Scheme Group" (the fresh-scheme entry button) calls before
    revealing the 6 mode buttons, so a fresh scheme genuinely starts
    fresh rather than showing whatever screen/results happened to be
    left over from a previously active scheme.

    Deliberately NOT called by "Load Prefilled Global Scheme Group" --
    resuming means leaving every one of these exactly as it was left,
    by design (see the project decision on this).

    Deliberately does NOT touch: state["mode"] (which tab is showing),
    state["active_scheme"]/"scheme_group_called" (Global Scheme Context
    itself), anything seating_*/manual_*  (Seating Chart, a separate
    mode entirely), or anything auth-related.
    """
    # ---------------- shared ----------------
    state["enrollment_text"] = ""
    state["completed"] = set()

    # ---------------- Train ----------------
    state["train_enrollments_text"] = ""
    state["train_step"] = "input"
    state["train_fetch_log"] = []
    state["captcha_pending"] = None
    state["train_fetch_current_task"] = None
    state["train_fetch_stop_requested"] = False
    state["train_samples"] = {}
    state["train_warnings"] = []
    state["train_order"] = []
    state["train_current_idx"] = 0
    state["train_mapping"] = {}
    state["train_collected"] = {key: [] for key, _ in mt.GROUPS}
    state["train_import_checked"] = True
    state["train_pending_rects"] = {}
    state["train_anchor"] = {}
    state["train_last_active_position"] = None
    state["train_institute_name"] = ""
    state["train_institute_address"] = ""
    state["train_cell_text"] = {}
    state["train_wizard_anchor"] = None
    state["train_wizard_pending"] = None
    state["train_whole_table_drag"] = None
    state["train_subjects_drag"] = None
    state["train_subjects_preview"] = []
    state["train_orientation"] = None
    state["train_level_count"] = None
    state["train_level_drags"] = [None] * mt.MAX_TEMPLATE_LEVELS
    state["train_level_card_containers"] = {}
    state["train_level_hint_labels"] = {}
    state["train_subjects_count_label"] = None
    state["train_values_drag"] = None
    state["train_last_trained_subjects"] = []
    state["train_last_trained_nodes"] = []
    state["train_preview_records"] = []
    state["train_preview_review"] = []
    state["train_preview_enr"] = None
    state["train_cell_elements"] = {}
    state["train_group_icons"] = {}

    # ---------------- Extract ----------------
    state["extract_step"] = "idle"
    state["extract_log"] = []
    state["extract_summary"] = None
    state["extract_review_details"] = []
    state["extract_total"] = 0
    state["extract_done_list"] = []
    state["extract_pending_list"] = []
    state["extract_stop_requested"] = False

    # ---------------- Course Codes ----------------
    state["coursecode_data"] = None
    state["coursecode_values"] = {}
    state["coursecode_faculty_values"] = {}
    state["coursecode_faculty_touched"] = set()
    state["coursecode_autofill"] = False
    state["coursecode_autofilled_keys"] = set()

    # ---------------- Report ----------------
    state["report_step"] = "select"
    state["report_log"] = []
    state["report_generated_files"] = []
    state["report_panel_open"] = []
    state["report_panel_container"] = None
    state["yearly_report_mode"] = "gap_check"
    state["yearly_gaps"] = []
    state["yearly_gap_upload_path"] = None
    state["yearly_gap_upload_name"] = None
    state["yearly_gap_matches"] = []
    state["k7c_reference_semester"] = None
    state["k7c_level1_draft"] = None
    state["k7c_fa_draft"] = None
    state["k7c_sa_draft"] = None
    state["report_selection"] = {
        "semester": {"enabled": True, "statuses": []},
        "yearly_result": {"enabled": False, "statuses": []},
        "k7_partb": {"enabled": True, "statuses": [], "fail_threshold": 30.0},
        "k7_partc": {"enabled": True, "statuses": []},
        "yearly_eligibility": {"enabled": False, "statuses": []},
        "topper_list": {"enabled": True, "statuses": []},
        "bright_weak": {"enabled": True, "statuses": [], "weak_threshold": 40.0, "bright_threshold": 75.0},
        "departmental": {"enabled": False, "statuses": [], "show_pct": False},
    }
    state["dept_loaded_key"] = None
    state["dept_classes_draft"] = []
    state["dept_mapping_draft"] = {}
    state["dept_enrolled_draft"] = {}
    state["dept_program_code_draft"] = ""
    state["dept_sem_off_draft"] = set()
    state["dept_open"] = {}

    # ---------------- Recheck ----------------
    state["recheck_step"] = "choose"
    state["recheck_log"] = []
    state["recheck_summary"] = None
    state["recheck_queue_mode"] = None
    state["recheck_queue_list"] = []
    state["recheck_queue_pos"] = 0
    state["recheck_queue_stats"] = {}
    state["recheck_queue_log"] = []
    state["recheck_manual_enrollment"] = ""
    state["recheck_manual_records"] = None
    state["recheck_manual_semesters"] = []
    state["recheck_manual_subject_names"] = {}
    state["recheck_manual_components"] = {}
    state["recheck_manual_values"] = {}
    state["recheck_manual_originals"] = {}
    state["recheck_manual_delete_semesters"] = set()
    state["recheck_delete_semesters_present"] = []
    state["recheck_manual_subjectwise_values"] = {}
    state["recheck_manual_subjectwise_originals"] = {}
    state["recheck_manual_subjectwise_meta"] = {}

    # ---------------- Offline Import ----------------
    state["offline_step"] = "setup"
    state["offline_semester"] = ""
    state["offline_year"] = ""
    state["offline_program"] = ""
    state["offline_subject_count"] = 1
    state["offline_levels"] = 2
    state["offline_setup_locked"] = False
    state["offline_subjects"] = []
    state["offline_template"] = None
    state["offline_paste_text"] = ""
    state["offline_parsed_rows"] = None
    state["offline_parse_errors"] = []
    state["offline_saved_count"] = 0
    state["offline_save_errors"] = []


def select_active_scheme(decl):
    """The sidebar radio pick -- SELECTION ONLY, never creation. Computes
    this scheme's path and points mt.DB_FILE at it (via
    mt.set_active_scheme_db), so every mode's calls into msbte_tool.py
    (which all already pass db_path=mt.DB_FILE) transparently read/write
    this scheme's data once it's actually entered -- but does NOT call
    mt.ensure_scheme_db() here, deliberately: creating the file at radio-
    click time would make "does this scheme already have data" (the
    fresh vs. prefilled decision the user makes next) undetectable, since
    every scheme would immediately have a file the instant it was ever
    clicked, whether or not real work was ever done in it. See
    render_operational_entry_buttons() for where that decision actually
    happens, and where the file genuinely gets created for the first
    time (only by clicking "Call Global Scheme Group").

    `decl` is one entry from mt.list_all_scheme_declarations():
    {"institute", "program", "year", "session", "scheme"}.

    The six mode buttons are hidden immediately (scheme_group_called
    reset to False) -- picking a scheme is never enough on its own to
    unlock them; one of the two entry buttons must be explicitly clicked
    first. Also invalidates Course Codes' load-once cache
    (state["coursecode_data"]) so a later entry into that scheme starts
    clean rather than possibly holding a previous scheme's leftover data
    in memory.
    Also repoints mt.MAPPING_FILE at THIS department's own
    layout_mapping.json (scoped per institute/program/year, one level
    coarser than the scheme database itself -- see
    get_department_mapping_path()) -- same reasoning, same pattern as
    DB_FILE: every existing MAPPING_FILE reference in Train/Extract/
    Course Codes already reads the module-level constant, so reassigning
    it here is all that's needed for them to transparently follow this
    department, with no changes to those call sites themselves.

    Also repoints REPORTS_DIR (this module's own constant, not
    msbte_tool's) at THIS department's own reports/ folder -- same
    pattern again: _generate_and_collect() and download_yearly_gap_pdf()
    already just read the module-level REPORTS_DIR name directly, so
    reassigning it here is all that's needed.

    Also sets mt.ACTIVE_INSTITUTE/ACTIVE_PROGRAM (via
    mt.set_active_department_context) -- what the two Report-layer
    functions that read the SHARED SEATING_DB_FILE directly
    (_compute_student_status_full, compute_seating_chart_gap) filter by,
    so they never see another department's or institute's seating chart
    rows.

    Also blanks Train's and Extract's/Recheck's enrollment-paste
    textboxes (train_enrollments_text, enrollment_text) -- UNLIKE
    everything else in this function, this happens even when the user
    is about to click "Load Prefilled Global Scheme Group" (full
    resume, no other reset at all). These two boxes hold transient
    typed/pasted input for "what to fetch NEXT", not persisted results,
    so a previous scheme's leftover enrollment numbers sitting in them
    after a switch would be actively misleading (or worse, get
    re-fetched into the WRONG scheme's database) rather than useful to
    resume.
    """
    global REPORTS_DIR
    path = mt.scheme_db_path(decl["institute"], decl["program"], decl["year"], decl["session"], decl["scheme"])
    mt.set_active_scheme_db(path)
    mapping_path = mt.get_department_mapping_path(
        decl["institute"], decl["program"], decl["year"], decl["session"], decl["scheme"]
    )
    mt.set_active_department_mapping_file(mapping_path)
    REPORTS_DIR = mt.get_department_reports_dir(decl["institute"], decl["program"], decl["year"])
    mt.set_active_department_context(decl["institute"], decl["program"], decl["year"], decl["session"], decl["scheme"])
    state["active_scheme"] = decl
    state["scheme_group_called"] = False
    state["coursecode_data"] = None
    state["train_enrollments_text"] = ""
    state["enrollment_text"] = ""

    # Extract must start clean for the newly selected scheme: abort any run still
    # in flight (it would otherwise keep writing into the NEW scheme's database),
    # release a pending captcha, and clear the previous scheme's log/progress.
    state["extract_run_id"] += 1
    pending = state.get("captcha_pending")
    if pending:
        pending["result"]["value"] = ""
        pending["done"].set()
    state["extract_step"] = "idle"
    state["extract_log"] = []
    state["extract_summary"] = None
    state["extract_review_details"] = []
    _clear_extract_progress()
    # Same stale-data problem for Recheck / Report / Course Codes caches.
    invalidate_downstream_data()
    state["yearly_gaps"] = mt.load_yearly_gap_flags_from_db(mt.DB_FILE)


def _seating_year_session():
    """Year/Session currently typed in Seating Chart (whichever path is active)."""
    if state["seating_manual_mode"]:
        return state["seating_manual_year"], state["seating_manual_session"]
    return state["seating_paste_year"], state["seating_paste_session"]


def seating_sitting_found():
    """True only if THIS exact Year + Session combo has at least one declared scheme."""
    year, session = _seating_year_session()
    year_s = mt.sanitize_path_component(year)
    session_s = mt.sanitize_path_component(session).lower()
    if not year_s or not session_s or not state["logged_in"]:
        return False
    dept = state["logged_in"]
    return any(
        d["year"] == year_s and d["session"] == session_s
        for d in mt.list_all_scheme_declarations(
            dept["institute_name"], dept["department_name"], mt.SEATING_DB_FILE)
    )


def refresh_scheme_sidebar():
    """Re-render the sidebar scheme blocks after Year/Session change. If the
    active scheme no longer matches the typed combo, deselect it and lock the
    mode buttons again."""
    year, session = _seating_year_session()
    year_s = mt.sanitize_path_component(year)
    session_s = mt.sanitize_path_component(session).lower()
    act = state["active_scheme"]
    if act and (not seating_sitting_found() or act["year"] != year_s or act["session"] != session_s):
        state["active_scheme"] = None
        state["scheme_group_called"] = False
    render_scheme_picker(state["scheme_picker_container"])
    render_scheme_entry_buttons(state["scheme_entry_container"])
    render_operational_mode_buttons(state["operational_modes_container"])


def render_scheme_picker(container):
    """Sidebar block, right under the Seating Chart button -- single-
    select radio list of every (program, year, session, scheme)
    combination ever declared (via either the paste path or manual
    entry, see mt.list_all_scheme_declarations()), letting the user pick
    exactly one as the active Global Scheme Context. Rebuilt in place
    whenever a Seating Chart save/confirm could have changed the list."""
    if container is None:
        return
    container.clear()
    if not seating_sitting_found():
        return  # nothing shown until the typed Year + Session combo exists
    with container:
        dept = state["logged_in"]
        declarations = mt.list_all_scheme_declarations(
            dept["institute_name"], dept["department_name"], mt.SEATING_DB_FILE,
        )
        year, session = _seating_year_session()
        year_s = mt.sanitize_path_component(year)
        session_s = mt.sanitize_path_component(session).lower()
        declarations = [d for d in declarations if d["year"] == year_s and d["session"] == session_s]
        if not declarations:
            ui.label("No scheme(s) declared yet -- use Seating Chart first.").classes(
                "text-xs text-gray-400 italic px-2"
            )
            return

        def label_for(d):
            return f"{d['year']} / {d['session']} / {d['scheme']}"

        options = {label_for(d): d for d in declarations}
        current = state["active_scheme"]
        current_label = label_for(current) if current else None

        def on_pick(e):
            chosen = options[e.value]
            select_active_scheme(chosen)
            update_mode_buttons()
            render_scheme_picker(container)
            render_scheme_entry_buttons(state["scheme_entry_container"])
            render_operational_mode_buttons(state["operational_modes_container"])
            render_top_area()
            render_mode_content()

        with ui.card().classes("w-full border-2 border-primary").style("padding: 6px 10px;"):
            ui.label("Active Scheme").classes("text-xs font-bold uppercase text-primary")
            ui.radio(
                list(options.keys()), value=current_label, on_change=on_pick,
            ).props("dense")


def render_scheme_entry_buttons(container):
    """Sidebar block, right under the Active Scheme radio picker -- the
    fresh-vs-prefilled decision point. Picking a scheme (see
    select_active_scheme()) never creates its database or unlocks the 6
    mode buttons on its own; this is where that actually happens, and
    ONLY by an explicit click here.

    Shows nothing at all if no scheme is picked yet, or if this scheme's
    Global Scheme Group has already been called this session (the 6
    mode buttons are showing instead -- this block's job is done).

    Otherwise checks mt.scheme_db_exists() for the active scheme:
      - Doesn't exist (fresh) -> ONE button: "Call Global Scheme Group".
        Creates the database for the first time (mt.ensure_scheme_db),
        resets every operational mode to its starting state (see
        reset_all_operational_modes() -- a fresh scheme must never show
        another scheme's leftover screen/results), then unlocks the 6
        mode buttons.
      - Exists (prefilled) -> TWO buttons:
          "Load Prefilled Global Scheme Group" -- resume: unlocks the 6
          mode buttons WITHOUT resetting anything, so every mode reopens
          exactly as it was left.
          "Delete Prefilled Scheme Data" -- irreversible: after a Yes/
          Cancel confirmation, deletes the ENTIRE database file (via
          mt.delete_scheme_db) -- not just emptying it. Never touches
          Seating Chart or the scheme's declaration, so the scheme stays
          selectable and correctly reverts to "fresh" afterward.
    """
    if container is None:
        return
    container.clear()

    decl = state["active_scheme"]
    if decl is None or state["scheme_group_called"]:
        return

    with container:
        exists = mt.scheme_db_exists(decl["institute"], decl["program"], decl["year"], decl["session"], decl["scheme"])

        def refresh_all():
            render_scheme_entry_buttons(container)
            render_operational_mode_buttons(state["operational_modes_container"])
            update_mode_buttons()
            render_top_area()
            render_mode_content()

        if not exists:
            def do_call_fresh():
                mt.ensure_scheme_db(decl["institute"], decl["program"], decl["year"], decl["session"], decl["scheme"])
                reset_all_operational_modes()
                state["scheme_group_called"] = True
                ui.notify("Fresh scheme -- all modes reset and ready.", type="positive")
                refresh_all()

            ui.button(
                "Call Global Scheme Group", icon="play_circle", on_click=do_call_fresh,
            ).classes("w-full").props("unelevated color=primary dense")
        else:
            def do_load_prefilled():
                state["scheme_group_called"] = True
                ui.notify("Resumed -- exactly as you left it.", type="positive")
                refresh_all()

            def ask_delete():
                with ui.dialog() as dialog, ui.card():
                    ui.label(
                        f"Permanently delete ALL data for {decl['year']} / {decl['session']} / "
                        f"{decl['scheme']}?"
                    ).classes("text-sm")
                    ui.label(
                        "This deletes the entire database -- every trained semester, extracted "
                        "student, course code, and report -- not just clearing it. Seating Chart "
                        "data is NOT affected. This cannot be undone."
                    ).classes("text-xs text-red-600 mt-1")

                    def do_delete_confirmed():
                        dialog.close()
                        deleted = mt.delete_scheme_db(
                            decl["institute"], decl["program"], decl["year"], decl["session"], decl["scheme"],
                        )
                        if deleted:
                            ui.notify("Scheme data deleted -- back to fresh.", type="warning")
                        refresh_all()

                    with ui.row().classes("w-full justify-end gap-2 mt-3"):
                        ui.button("Cancel", on_click=dialog.close).props("outline")
                        ui.button("Yes, Delete", color="negative", on_click=do_delete_confirmed)
                dialog.open()

            ui.button(
                "Load Prefilled Global Scheme Group", icon="play_circle", on_click=do_load_prefilled,
            ).classes("w-full").props("unelevated color=primary dense")
            ui.button(
                "Delete Prefilled Scheme Data", icon="delete_forever", on_click=ask_delete,
            ).classes("w-full mt-1").props("outline color=negative dense")


def render_operational_mode_buttons(container):
    """The Global Scheme Group's own buttons -- Train, Extract, Course
    Codes, Offline Import, Recheck, Report. Absent from the sidebar
    entirely (not just walled/disabled) until the CURRENTLY active
    scheme's Global Scheme Group has actually been called -- picking a
    scheme in the radio picker alone is never enough (see
    select_active_scheme() and render_scheme_entry_buttons()); one of
    "Call Global Scheme Group" or "Load Prefilled Global Scheme Group"
    must be explicitly clicked first. Rebuilt in place whenever the
    active scheme changes or its Group is (re-)called."""
    if container is None:
        return
    container.clear()
    if not state["scheme_group_called"]:
        return
    with container:
        for key, label, icon in MODES:
            if key == "seating":
                continue
            btn = ui.button(
                label, icon=icon, on_click=lambda k=key: select_mode(k)
            ).props("align=left unelevated").classes("w-full justify-start")
            mode_buttons[key] = btn


def render_department_sitting_picker(year_key, session_key):
    """Clickable cards for every seating chart database this department
    already has (Year / Session + semesters, schemes, row count). Writes the
    chosen sitting into state[year_key]/state[session_key], so it works for
    both the paste path ("seating_paste_*") and Manual Entry ("seating_manual_*").
    Returns True if any database exists."""
    dept = state["logged_in"]
    existing = mt.list_department_seating_chart_dbs(dept["institute_name"], dept["department_name"])

    def select_sitting(year, session):
        state[year_key] = year
        state[session_key] = session
        state["seating_parsed_rows"] = None
        state["seating_parse_errors"] = []
        refresh_scheme_sidebar()
        render_mode_content()

    if not existing:
        ui.label("No seating chart database exists yet for this department.").classes("text-xs text-gray-500")
        return False

    ui.label("Seating charts already saved -- choose Process to continue with one, or Delete to remove it:").classes(
        "text-xs text-gray-500"
    )
    with ui.row().classes("w-full gap-3 mt-2 flex-wrap"):
        for entry in existing:
            is_active = (
                mt.sanitize_path_component(state[year_key]) == entry["year"]
                and state[session_key].lower() == entry["session"].lower()
            )
            card_cls = "w-64 cursor-pointer " + ("border-2 border-primary bg-blue-50" if is_active else "border")
            with ui.card().classes(card_cls).on(
                "click", lambda e, en=entry: select_sitting(en["year"], en["session"])
            ):
                ui.label(f"{entry['year']} / {entry['session']}").classes("text-sm font-bold")
                sems = ", ".join(s.title() for s in entry["semesters"]) or "(no rows)"
                ui.label(f"Semesters: {sems}").classes("text-xs text-gray-600")
                ui.label(f"Schemes: {', '.join(entry['schemes']) or '-'}  |  {entry['rows']} row(s)").classes(
                    "text-xs text-gray-500"
                )
                with ui.row().classes("w-full gap-2 mt-1"):
                    ui.button("Process", icon="play_arrow").props("dense unelevated color=primary").on(
                        "click.stop", lambda e, en=entry: select_sitting(en["year"], en["session"])
                    )
                    ui.button("Delete", icon="delete").props("dense outline color=negative").on(
                        "click.stop", lambda e, en=entry: confirm_delete_sitting(en["year"], en["session"])
                    )
    return True


def render_seating_content(container):
    with container:
        with ui.card().classes("w-full"):
            with ui.row().classes("w-full items-start justify-between"):
                with ui.column().classes("gap-0"):
                    ui.label("Seating Chart").classes("text-xl font-bold")
                    ui.label(MODE_DESCRIPTIONS["seating"]).classes("text-sm text-gray-600")
                ui.button(
                    "Delete All Seating Chart Data", icon="delete_forever",
                    on_click=confirm_wipe_seating_chart,
                ).props("unelevated color=negative")

        if state["seating_manual_mode"]:
            render_seating_manual_entry()
            return

        dept = state["logged_in"]

        with ui.card().classes("w-full mt-3 border-2 border-primary"):
            ui.label("Step 1: Which exam sitting is this?").classes("text-md font-semibold")

            # ---- Option A: existing databases, shown first ----
            if render_department_sitting_picker("seating_paste_year", "seating_paste_session"):
                ui.separator().classes("my-3")

            # ---- Option B: new seating chart ----
            ui.label("Or load a NEW seating chart -- enter the Year and choose the Session:").classes(
                "text-xs text-gray-500"
            )
            with ui.row().classes("w-full gap-3 items-center mt-2"):
                ui.input(label="Department", value=dept["department_name"]).classes("flex-1").props(
                    "outlined dense readonly"
                )

                def on_paste_year(e):
                    # Just remember the text -- re-rendering here would rebuild the
                    # input and drop the cursor after every keystroke.
                    state["seating_paste_year"] = e.value

                def apply_paste_year(e=None):
                    refresh_scheme_sidebar()
                    render_mode_content()

                def on_paste_session(e):
                    state["seating_paste_session"] = e.value
                    refresh_scheme_sidebar()
                    render_mode_content()

                year_input = ui.input(label="Year (e.g. 2025-2026)", value=state["seating_paste_year"],
                                      on_change=on_paste_year).classes("flex-1").props("outlined dense")
                year_input.on("blur", apply_paste_year)
                year_input.on("keydown.enter", apply_paste_year)
                ui.select(["Odd", "Even"], label="Session", value=state["seating_paste_session"],
                          on_change=on_paste_session).classes("flex-1").props("outlined dense")

        dept = state["logged_in"]
        # ---------------- Import from Institute Seating Chart ----------------
        inst_dbs = mt.list_institute_seating_chart_dbs(dept["institute_name"])
        with ui.card().classes("w-full mt-3"):
            ui.label("Import from Institute Seating Chart").classes("text-md font-semibold")
            if not inst_dbs:
                ui.label("No Institute Seating Chart has been saved for this institute yet.").classes(
                    "text-xs text-gray-500"
                )
            else:
                ui.label(
                    "Pick an institute sitting, then the Program Code that is YOUR department "
                    "and the semesters you want. The rows are copied into this department's "
                    "seating chart for that same Year/Session (the institute data is not changed)."
                ).classes("text-xs text-gray-500")
                chosen = state["seating_import_sitting"]
                with ui.row().classes("w-full gap-2 mt-2 flex-wrap"):
                    for entry in inst_dbs:
                        def pick_inst(en=entry):
                            state["seating_import_sitting"] = {"year": en["year"], "session": en["session"]}
                            state["seating_import_program"] = None
                            state["seating_import_semesters"] = []
                            render_mode_content()

                        active = bool(chosen) and chosen["year"] == entry["year"] and chosen["session"] == entry["session"]
                        ui.button(
                            f"{entry['year']} / {entry['session']}", icon="account_balance", on_click=pick_inst,
                        ).props(f"{'unelevated color=primary' if active else 'outline'} dense")

                if chosen:
                    options = mt.get_institute_import_options(dept["institute_name"], chosen["year"], chosen["session"])
                    if not options:
                        ui.label("That institute sitting has no data.").classes("text-xs text-orange-600 mt-2")
                    else:
                        def on_import_program(code, checked):
                            # Single choice: ticking one code unticks the others; unticking clears it.
                            if checked:
                                state["seating_import_program"] = code
                                state["seating_import_semesters"] = [
                                    x["semester_label"] for x in options.get(code, [])
                                ]  # default: all semesters of that program
                            elif state["seating_import_program"] == code:
                                state["seating_import_program"] = None
                                state["seating_import_semesters"] = []
                            render_mode_content()

                        ui.label(
                            f"Program Codes found in this institute sitting ({len(options)}) -- "
                            "tick ONE (your department):"
                        ).classes("text-xs font-semibold mt-2")
                        with ui.row().classes("w-full gap-4 flex-wrap"):
                            for code, sems_list in options.items():
                                total = sum(x["count"] for x in sems_list)
                                ui.checkbox(
                                    f"{code}  ({total} row(s))",
                                    value=(state["seating_import_program"] == code),
                                    on_change=lambda e, cd=code: on_import_program(cd, e.value),
                                )

                        prog = state["seating_import_program"]
                        if prog in options:
                            sem_opts = {
                                x["semester_label"]: (
                                    f"{x['semester_label'].title()} -- {x['count']} row(s), "
                                    f"scheme(s) {', '.join(x['schemes'])}"
                                )
                                for x in options[prog]
                            }

                            def on_import_sems(e):
                                state["seating_import_semesters"] = e.value or []

                            ui.select(
                                sem_opts, label="Semesters available -- choose which to import",
                                value=state["seating_import_semesters"], multiple=True, on_change=on_import_sems,
                            ).classes("w-full mt-2").props("outlined dense use-chips")

                            def do_import():
                                sems = state["seating_import_semesters"]
                                if not sems:
                                    ui.notify("Choose at least one semester to import.", type="warning")
                                    return
                                saved, errors, schemes = mt.import_department_seating_from_institute(
                                    dept["institute_name"], dept["department_name"],
                                    chosen["year"], chosen["session"], prog, sems,
                                )
                                if saved == 0:
                                    ui.notify("; ".join(errors) or "Nothing imported.", type="negative")
                                    return
                                # Make the imported sitting the selected one.
                                state["seating_paste_year"] = chosen["year"]
                                state["seating_paste_session"] = chosen["session"]
                                state["seating_manual_mode"] = False
                                state["seating_parsed_rows"] = None
                                state["seating_parse_errors"] = []
                                msg = f"Imported {saved} row(s) -- scheme(s): {', '.join(schemes)}."
                                if errors:
                                    msg += f" {len(errors)} row(s) skipped."
                                ui.notify(msg, type="positive" if not errors else "warning")
                                render_mode_content()
                                refresh_scheme_sidebar()

                            ui.button(
                                "Import into this Department", icon="download", on_click=do_import,
                            ).classes("mt-3").props("unelevated color=primary")

        year_typed = state["seating_paste_year"].strip()
        session_typed = state["seating_paste_session"]
        _data_already_exists = False
        if year_typed:
            _data_already_exists = seating_sitting_found()
            if _data_already_exists:
                with ui.card().classes("w-full mt-3 bg-green-50 border-2 border-green-600"):
                    ui.label(
                        f"Seating chart data already exists for {year_typed} / {session_typed} -- "
                        f"shown below. You can still paste more rows further down to add to it "
                        f"or correct anything, or go straight to Scheme selection in the sidebar."
                    ).classes("text-sm text-green-800 font-semibold")
            else:
                with ui.card().classes("w-full mt-3 bg-orange-50 border-2 border-orange-400"):
                    ui.label(
                        f"No seating chart data found for {year_typed} / {session_typed}. "
                        f"Please continue with \"Fill in each column from MSBTE's seating "
                        f"chart Excel\" below."
                    ).classes("text-sm text-orange-800 font-semibold")

        with ui.card().classes("w-full mt-3"):
            ui.label("Fill in each column from MSBTE's seating chart Excel").classes("text-md font-semibold")
            ui.label(

                "Six separate boxes, one per column -- paste (or type) that column's values, "
                "one per line, in the SAME row order in every box (line 1 of every box = "
                "row 1, line 2 = row 2, and so on)."
            ).classes("text-xs text-gray-500")
            ui.label(
                "Semester-Scheme code format: \"X-N-S\" (e.g. \"TX-4-K\") -- N is the "
                "semester number (1-6), S is the scheme letter (K, I, ...). The leading "
                "segment (\"TX\") is not used."
            ).classes("text-xs text-gray-500")
            ui.label(
                "These boxes are the GLOBAL, persistent seating chart source -- they stay "
                "filled in after Save (do not clear), and are fully re-combined into rows "
                "each time you Save. Re-saving a row for an enrollment+semester+scheme "
                "that's already saved replaces it -- safe to correct and re-save."
            ).classes("text-xs text-gray-500 font-semibold")

            ui.separator().classes("my-2")

            with ui.row().classes("w-full gap-3 mt-2 flex-nowrap overflow-x-auto"):
                for key, label in SEATING_COLUMN_SPECS:
                    with ui.column().classes("flex-1 min-w-48"):
                        ui.label(label).classes("text-xs font-semibold")

                        def on_col_change(e, k=key):
                            state["seating_columns"][k] = e.value

                        ui.textarea(
                            placeholder="One value per line...",
                            value=state["seating_columns"][key],
                            on_change=on_col_change,
                        ).classes("w-full").props("outlined rows=8 dense")

            def parse_rows():
                cols = state["seating_columns"]
                split = {}
                for key, _label in SEATING_COLUMN_SPECS:
                    text = (cols[key] or "").replace("\r\n", "\n").replace("\r", "\n")
                    split[key] = text.split("\n") if text.strip() else []
                # Trim a trailing blank line every box tends to end with
                # (from a final Enter/newline), but only if EVERY box's
                # last line is blank -- avoids silently dropping a
                # genuinely blank-but-intentional trailing value in one
                # column while others still have data there.
                lengths = [len(v) for v in split.values() if v]
                if not lengths:
                    ui.notify("Fill in at least the Enrollment Number column first.", type="warning")
                    return
                if all((split[k][-1].strip() == "" if split[k] else True) for k, _ in SEATING_COLUMN_SPECS):
                    for k in split:
                        if split[k] and split[k][-1].strip() == "":
                            split[k] = split[k][:-1]

                n_rows = max((len(v) for v in split.values()), default=0)
                errors = []
                rows = []
                for i in range(n_rows):
                    row = []
                    mismatch = False
                    for key, label in SEATING_COLUMN_SPECS:
                        col_vals = split[key]
                        if i >= len(col_vals):
                            errors.append(f"Row {i + 1}: '{label}' column has no value here "
                                          f"(only {len(col_vals)} line(s) in that box) -- row skipped")
                            mismatch = True
                            break
                        row.append(col_vals[i].strip())
                    if not mismatch:
                        rows.append(row)

                state["seating_parsed_rows"] = rows
                state["seating_parse_errors"] = errors
                render_mode_content()

            ui.button("Parse", icon="playlist_add_check", on_click=parse_rows).classes("mt-2").props(
                "unelevated color=primary"
            )

        rows = state["seating_parsed_rows"]
        if rows is not None:
            with ui.card().classes("w-full mt-3"):
                ui.label(f"Preview -- {len(rows)} row(s) parsed").classes("text-md font-semibold")
                if state["seating_parse_errors"]:
                    ui.label("Column-count problems (fix in your paste and re-Parse):").classes(
                        "text-xs text-red-600 font-semibold mt-1"
                    )
                    for err in state["seating_parse_errors"][:20]:
                        ui.label(f"- {err}").classes("text-xs text-red-600")

                # Preview table shows the derived Semester + Scheme columns
                # (parsed live from the raw code) alongside the raw code
                # itself, so a bad "TX-4-K" is visible before Save.
                columns = [
                    {"name": "c0", "label": "Enrollment No", "field": "c0"},
                    {"name": "c1", "label": "Student Name", "field": "c1"},
                    {"name": "c2", "label": "Seat No", "field": "c2"},
                    {"name": "c3", "label": "Semester-Scheme Code", "field": "c3"},
                    {"name": "c3a", "label": "-> Semester", "field": "c3a"},
                    {"name": "c3b", "label": "-> Scheme", "field": "c3b"},
                    {"name": "c4", "label": "Regular/EX", "field": "c4"},
                    {"name": "c5", "label": "Subject Appeared", "field": "c5"},
                ]
                table_rows = []
                for r in rows[:20]:
                    sem_scheme_raw = r[3] if len(r) > 3 else ""
                    sem_label, scheme, err = mt.parse_semester_scheme_code(sem_scheme_raw)
                    table_rows.append({
                        "c0": r[0] if len(r) > 0 else "", "c1": r[1] if len(r) > 1 else "",
                        "c2": r[2] if len(r) > 2 else "", "c3": sem_scheme_raw,
                        "c3a": sem_label.title() if sem_label else f"\u26a0 {err}",
                        "c3b": scheme or "",
                        "c4": r[4] if len(r) > 4 else "", "c5": r[5] if len(r) > 5 else "",
                    })
                ui.table(columns=columns, rows=table_rows).classes("w-full mt-2").props("dense")
                if len(rows) > 20:
                    ui.label(f"...showing first 20 of {len(rows)} rows.").classes("text-xs text-gray-500 mt-1")

                def save_rows():
                    dept = state["logged_in"]
                    institute = dept["institute_name"]
                    program = dept["department_name"]
                    year = state["seating_paste_year"]
                    session = state["seating_paste_session"]
                    if not year.strip():
                        ui.notify("Fill in Year first.", type="warning")
                        return

                    saved, errors = mt.save_seating_chart_rows(
                        institute, program, year, session, state["seating_parsed_rows"],
                    )
                    state["seating_last_saved_count"] = saved
                    state["seating_last_save_errors"] = errors

                    # Every scheme now present in the seating chart gets its
                    # own database created (idempotent -- an already-created
                    # scheme's database is left untouched), named from this
                    # department's Institute/Program plus this paste path's
                    # own Year/Session.
                    schemes_now = mt.list_active_schemes(institute, program, year, session)
                    for scheme in schemes_now:
                        mt.ensure_scheme_db(institute, program, year, session, scheme)
                        mt.record_scheme_declaration(institute, program, year, session, scheme, source="paste")

                    # GLOBAL box: deliberately NOT cleared here (unlike the
                    # old behavior) -- it stays as the persistent source of
                    # truth, re-parsed fresh on every future Save.
                    state["seating_parsed_rows"] = None
                    state["seating_parse_errors"] = []
                    # IMPORTANT: notify BEFORE the render_* calls below --
                    # those clear/rebuild content_container, which destroys
                    # this very button's own slot; calling ui.notify()
                    # afterward tries to resolve a now-deleted slot and
                    # raises "The parent element this slot belongs to has
                    # been deleted."
                    ui.notify(f"Saved {saved} seating chart row(s).", type="positive")
                    render_mode_content()
                    refresh_scheme_sidebar()

                ui.button("Save to Database", icon="save", on_click=save_rows).classes("mt-3").props(
                    "unelevated color=primary"
                )

        if state["seating_last_saved_count"] is not None:
            with ui.card().classes("w-full mt-3"):
                ui.label(f"Last save: {state['seating_last_saved_count']} row(s) saved.").classes(
                    "text-sm text-green-700 font-semibold"
                )
                if state["seating_last_save_errors"]:
                    ui.label("Some rows were skipped:").classes("text-xs text-red-600 font-semibold mt-1")
                    for err in state["seating_last_save_errors"][:20]:
                        ui.label(f"- {err}").classes("text-xs text-red-600")

        dept = state["logged_in"]
        summary = mt.get_seating_chart_summary(
            dept["institute_name"], dept["department_name"],
            state["seating_paste_year"], state["seating_paste_session"],
        )
        if not summary["schemes"]:
            with ui.card().classes("w-full mt-3"):
                ui.label("No seating chart data yet.").classes("text-xs text-gray-500 mt-1")
            render_seating_manual_entry_link()
            return

        ui.label(
            f"{len(summary['schemes'])} scheme(s) detected: {', '.join(summary['schemes'])} -- "
            f"each scheme's breakdown, enrollment lists, and Train-mode recommendations are below."
        ).classes("text-sm font-semibold mt-4")

        for scheme in summary["schemes"]:
            scheme_data = summary["by_scheme"][scheme]
            with ui.card().classes("w-full mt-3 border-2 border-primary"):
                ui.label(f"Scheme: {scheme}").classes("text-lg font-bold text-primary")

                ui.label("Semester-wise Counts").classes("text-md font-semibold mt-2")
                if not scheme_data["by_semester"]:
                    ui.label("No data yet for this scheme.").classes("text-xs text-gray-500 mt-1")
                cats = scheme_data["categories"]
                for sem in scheme_data["by_semester"]:
                    counts_txt = "   ".join(f"{c}: {sem['counts'][c]}" for c in cats)
                    with ui.expansion(
                        f"{sem['semester_label']}    {counts_txt}   Total: {sem['total_count']}"
                    ).classes("w-full border-b"):
                        with ui.row().classes("w-full gap-6"):
                            for c in cats:
                                with ui.column().classes("flex-1"):
                                    ui.label(f"{c} students ({sem['counts'][c]})").classes(
                                        "text-xs font-semibold text-gray-600"
                                    )
                                    for s in sem["students"][c]:
                                        ui.label(
                                            f"{s['enrollment']}  --  {s['student_name']}  (Seat {s['seat_number']})"
                                        ).classes("text-xs")

                gt = scheme_data["grand_total"]
                ui.label(f"All Semesters ({scheme}) Combined").classes("text-md font-semibold mt-3")
                gt_txt = "      ".join(f"{c}: {gt['counts'][c]}" for c in cats)
                ui.label(f"{gt_txt}      Total: {gt['total_count']}").classes("text-sm mt-1")
                ui.label(
                    "(counts every semester-row separately within this scheme -- the same "
                    "student appearing in 3 semesters counts as 3 here)"
                ).classes("text-xs text-gray-500")

                unique = scheme_data["unique_enrollments"]
                ui.label(f"Unique Enrollment Numbers ({scheme})  ({len(unique)} unique students)").classes(
                    "text-md font-semibold mt-3"
                )
                ui.label(f"For feeding into {scheme}-scheme's Train mode later.").classes("text-xs text-gray-500")
                unique_text = "\n".join(unique)
                ui.textarea(value=unique_text).classes("w-full mt-2").props("outlined rows=6 readonly")

                def copy_unique(t=unique_text):
                    ui.run_javascript(f"navigator.clipboard.writeText({json.dumps(t)})")
                    ui.notify("Copied to clipboard.", type="positive")

                ui.button(f"Copy {scheme} List", icon="content_copy", on_click=copy_unique).classes("mt-2").props(
                    "outlined"
                )

                # --- Recommended Train-mode sample enrollments: the
                # SMALLEST set of enrollments (greedy minimum set cover,
                # see mt.compute_train_sample_enrollments) whose combined
                # semester coverage spans every semester this scheme has,
                # so Train mode doesn't need one sample fetch per semester
                # -- one enrollment covering 4 semesters at once is enough
                # for those 4, and only the remaining uncovered semesters
                # need another enrollment. ---
                cover = mt.compute_train_sample_enrollments(
                    dept["institute_name"], dept["department_name"],
                    state["seating_paste_year"], state["seating_paste_session"], scheme,
                )
                ui.label(f"Recommended Enrollment Numbers for Train Mode ({scheme})").classes(
                    "text-md font-semibold mt-4"
                )
                ui.label(
                    "Smallest set of enrollments that, together, cover EVERY semester this "
                    "scheme has -- fetch these few in Train mode instead of one sample per "
                    "semester. Each line below shows which semester(s) that enrollment "
                    "newly contributes."
                ).classes("text-xs text-gray-500")
                if not cover:
                    ui.label("No coverage data yet for this scheme.").classes("text-xs text-gray-500 mt-1")
                else:
                    if len(cover) > 6:
                        ui.label(
                            f"\u26a0 {len(cover)} enrollment(s) needed to cover every semester -- "
                            f"more than Train mode's 6 sample-enrollment boxes. You may need two "
                            f"Train mode passes to cover them all."
                        ).classes("text-xs text-orange-600 font-semibold mt-1")

                    with ui.column().classes("gap-1 mt-2"):
                        for item in cover:
                            new_sems = ", ".join(s.title() for s in item["new_semesters"])
                            all_sems = ", ".join(s.title() for s in item["semesters_covered"])
                            ui.label(f"{item['enrollment']}  --  new: {new_sems}").classes(
                                "text-xs font-semibold"
                            )
                            if item["semesters_covered"] != item["new_semesters"]:
                                ui.label(f"    (also has: {all_sems})").classes("text-xs text-gray-500")

                    cover_text = "\n".join(item["enrollment"] for item in cover)
                    ui.textarea(value=cover_text).classes("w-full mt-2").props("outlined rows=4 readonly")

                    def copy_cover(t=cover_text):
                        ui.run_javascript(f"navigator.clipboard.writeText({json.dumps(t)})")
                        ui.notify("Copied to clipboard.", type="positive")

                    ui.button(
                        f"Copy {scheme} Train Sample List", icon="content_copy", on_click=copy_cover,
                    ).classes("mt-2").props("outlined")

        render_seating_manual_entry_link()


def render_seating_manual_entry_link():
    """Bottom-of-screen escape hatch: for when there's genuinely no
    seating chart available at all. Switches to the self-contained
    manual-entry form (see render_seating_manual_entry()) -- mutually
    exclusive with the paste-based path above; picking this hides the
    paste form entirely rather than the two coexisting."""
    with ui.card().classes("w-full mt-3"):
        ui.label(
            "Seating chart not available? You can declare scheme(s) manually instead."
        ).classes("text-xs text-gray-500")

        def switch_to_manual():
            state["seating_manual_mode"] = True
            render_mode_content()

        ui.button(
            "Seating Chart Not Available -- Manual Entry", icon="edit_note", on_click=switch_to_manual,
        ).classes("mt-1").props("outline")


def render_seating_manual_entry():
    """Self-contained alternative to the paste-based path -- own
    Program/Year/Session fields (never shared with the paste path's),
    a "how many schemes" count, and that many single-letter scheme
    textboxes. On Confirm, each declared letter gets a database created
    exactly like the paste path's Save does -- from that point on there
    is NO difference between a manually-declared scheme and a
    paste-detected one anywhere downstream."""
    with ui.card().classes("w-full mt-3"):
        with ui.row().classes("w-full items-center justify-between"):
            ui.label("Manual Scheme Entry").classes("text-lg font-bold")

            def switch_to_paste():
                state["seating_manual_mode"] = False
                render_mode_content()

            ui.button(
                "Back to Seating Chart Paste", icon="arrow_back", on_click=switch_to_paste,
            ).props("outline dense")

        ui.label(
            "For when no seating chart is available at all. Describe this exam sitting, "
            "then declare which scheme(s) exist -- each gets its own database created, "
            "exactly as if it had been detected from a real seating chart paste."
        ).classes("text-xs text-gray-500 mt-1")

        ui.separator().classes("my-2")
        render_department_sitting_picker("seating_manual_year", "seating_manual_session")
        ui.label("Or declare schemes for a NEW sitting -- enter the Year and choose the Session:").classes(
            "text-xs text-gray-500 mt-2"
        )
        with ui.row().classes("w-full gap-3 items-center"):
            dept = state["logged_in"]
            ui.input(label="Department", value=dept["department_name"]).classes("flex-1").props(
                "outlined dense readonly"
            )

            def on_manual_year(e):
                state["seating_manual_year"] = e.value
                refresh_scheme_sidebar()

            def on_manual_session(e):
                state["seating_manual_session"] = e.value
                refresh_scheme_sidebar()

            ui.input(label="Year", value=state["seating_manual_year"],
                      on_change=on_manual_year).classes("flex-1").props("outlined dense")
            ui.select(["Odd", "Even"], label="Session", value=state["seating_manual_session"],
                       on_change=on_manual_session).classes("flex-1").props("outlined dense")
        ui.separator().classes("my-2")

        def on_scheme_count_change(e):
            raw = (e.value or "").strip()
            try:
                n = max(0, min(26, int(raw)))  # sane ceiling -- at most one box per letter of the alphabet
            except ValueError:
                n = 0
            state["seating_manual_scheme_count"] = raw
            letters = state["seating_manual_scheme_letters"]
            if n > len(letters):
                letters.extend([""] * (n - len(letters)))
            else:
                del letters[n:]
            render_mode_content()

        ui.input(
            label="Number of schemes", value=state["seating_manual_scheme_count"],
            on_change=on_scheme_count_change,
        ).classes("w-48").props("outlined dense")

        letters = state["seating_manual_scheme_letters"]
        if letters:
            with ui.row().classes("w-full gap-3 mt-2 flex-wrap"):
                for i in range(len(letters)):
                    def on_letter_change(e, idx=i):
                        v = (e.value or "").strip()[:1]  # at most one character kept
                        state["seating_manual_scheme_letters"][idx] = v

                    ui.input(
                        label=f"Scheme {i + 1}", value=letters[i], on_change=on_letter_change,
                        validation={"Letters only, single character": lambda v: not v or v.strip().isalpha()},
                    ).classes("w-32").props("outlined dense maxlength=1")

            def confirm_manual_schemes():
                dept = state["logged_in"]
                institute = dept["institute_name"]
                program = dept["department_name"]
                year = state["seating_manual_year"]
                session = state["seating_manual_session"]
                if not year.strip():
                    ui.notify("Fill in Year first.", type="warning")
                    return

                raw_letters = [l.strip() for l in state["seating_manual_scheme_letters"]]
                if any(not l for l in raw_letters):
                    ui.notify("Every scheme box needs a letter -- none can be left blank.", type="warning")
                    return
                if any(not l.isalpha() or len(l) != 1 for l in raw_letters):
                    ui.notify("Each scheme box must be exactly one letter (no digits).", type="warning")
                    return

                normalized = [l.upper() for l in raw_letters]
                if len(set(normalized)) != len(normalized):
                    ui.notify("Duplicate scheme letters aren't allowed -- each must be unique.", type="warning")
                    return

                for scheme in normalized:
                    mt.ensure_scheme_db(institute, program, year, session, scheme)
                    mt.record_scheme_declaration(institute, program, year, session, scheme, source="manual")

                state["seating_manual_last_confirmed"] = normalized
                ui.notify(f"Declared {len(normalized)} scheme(s): {', '.join(normalized)}.", type="positive")
                render_mode_content()
                refresh_scheme_sidebar()

            ui.button(
                "Confirm Schemes", icon="check_circle", on_click=confirm_manual_schemes,
            ).classes("mt-3").props("unelevated color=primary")

        if state["seating_manual_last_confirmed"]:
            with ui.card().classes("w-full mt-3 border-2 border-primary"):
                ui.label(
                    f"Last confirmed: {', '.join(state['seating_manual_last_confirmed'])} -- "
                    f"database(s) created."
                ).classes("text-sm text-green-700 font-semibold")


def render_mode_content():
    try:
        content_container.clear()
    except RuntimeError:
        # Stale client from a page reload/reconnect that happened while
        # this async callback was still in flight. There's no live DOM
        # left to render into, so just stop here instead of crashing the
        # background task with a "parent slot deleted" error.
        return
    mode = state["mode"]

    if mode in MODE_ORDER + ["report"] and not state["scheme_group_called"]:
        with content_container:
            with ui.card().classes("w-full border-2 border-orange-300"):
                ui.label("Global Scheme Group not called yet").classes("text-lg font-bold text-orange-700")
                ui.label(
                    "Pick a scheme in the sidebar's Active Scheme list, then click "
                    "\"Call Global Scheme Group\" (or \"Load Prefilled Global Scheme Group\" "
                    "if that scheme already has data) to unlock this mode."
                ).classes("text-sm text-gray-600")
                ui.button(
                    "Go to Seating Chart", icon="event_seat", on_click=lambda: select_mode("seating"),
                ).classes("mt-2").props("outline")
        restore_scroll_positions()
        return

    if mode == "train":
        step = state["train_step"]
        if step == "input":
            render_train_input(content_container)
        elif step == "fetching":
            render_fetching(content_container)
        elif step == "select_ranges":
            render_select_ranges(content_container)
        elif step == "subjectwise_panel":
            render_subjectwise_panel(content_container)
        elif step == "wizard_done":
            render_wizard_done(content_container)
        elif step == "done":
            render_train_done(content_container)
        restore_scroll_positions()
        return

    if mode == "extract":
        step = state["extract_step"]
        if step == "idle":
            render_extract_idle(content_container)
        elif step == "running":
            render_extract_running(content_container)
        elif step == "done":
            render_extract_done(content_container)
        restore_scroll_positions()
        return

    if mode == "coursecodes":
        render_coursecodes(content_container)
        restore_scroll_positions()
        return

    if mode == "report":
        step = state["report_step"]
        if step == "select":
            render_report_select(content_container)
        elif step == "generating":
            render_report_generating(content_container)
        elif step == "done":
            render_report_done(content_container)
        restore_scroll_positions()
        return

    if mode == "seating":
        render_seating_content(content_container)
        restore_scroll_positions()
        return

    if mode == "offline":
        step = state["offline_step"]
        if step == "setup":
            render_offline_setup(content_container)
        elif step == "paste":
            render_offline_paste(content_container)
        elif step == "done":
            render_offline_done(content_container)
        restore_scroll_positions()
        return

    if mode == "recheck":
        step = state["recheck_step"]
        if step == "choose":
            render_recheck_choose(content_container)
        elif step == "automatic_running":
            render_recheck_automatic_running(content_container)
        elif step == "automatic_done":
            render_recheck_automatic_done(content_container)
        elif step == "queue_manual_editor":
            render_recheck_queue_manual_editor(content_container)
        elif step == "queue_manual_done":
            render_recheck_queue_manual_done(content_container)
        elif step == "queue_delete_editor":
            render_recheck_queue_delete_editor(content_container)
        elif step == "queue_delete_done":
            render_recheck_queue_delete_done(content_container)
        restore_scroll_positions()
        return

    with content_container:
        with ui.card().classes("w-full"):
            ui.label(dict((m[0], m[1]) for m in MODES)[mode]).classes("text-xl font-bold")
            ui.label(MODE_DESCRIPTIONS[mode]).classes("text-sm text-gray-600")
            ui.separator()
            ui.label("UI for this mode isn't wired up yet -- coming next.").classes(
                "text-gray-400 italic mt-4"
            )

            idx = MODE_ORDER.index(mode)
            is_last = idx == len(MODE_ORDER) - 1
            ui.button(
                "Mark Complete" if is_last else "Mark Complete \u2192 Next Mode",
                icon="check_circle",
                on_click=lambda m=mode: mark_complete_and_advance(m),
            ).classes("mt-4").props("outline color=positive")
    restore_scroll_positions()


def render_login_screen():
    ui.label("MSBTE Result Tool").classes("text-2xl font-bold mt-8")
    with ui.card().classes("w-96 mt-4"):
        with ui.tabs().classes("w-full") as tabs:
            institute_tab = ui.tab("Institute")
            department_tab = ui.tab("Department")
        with ui.tab_panels(tabs, value=institute_tab if state["login_type"] == "institute" else department_tab).classes("w-full") as panels:
            with ui.tab_panel(institute_tab):
                def on_inst_user(e):
                    state["login_institute_username"] = e.value

                def on_inst_pass(e):
                    state["login_institute_password"] = e.value

                ui.input(label="Username", value=state["login_institute_username"],
                          on_change=on_inst_user).classes("w-full").props("outlined dense")
                ui.input(label="Password", value=state["login_institute_password"], password=True,
                          on_change=on_inst_pass).classes("w-full mt-2").props("outlined dense")

                def do_institute_login():
                    res, err = mt.authenticate_institute(
                        state["login_institute_username"], state["login_institute_password"],
                    )
                    if res is None:
                        ui.notify(err, type="negative")
                        return
                    state["logged_in"] = {"type": "institute", **res}
                    ui.navigate.reload()

                ui.button("Login", icon="login", on_click=do_institute_login).classes("w-full mt-3").props(
                    "unelevated color=primary"
                )
                with ui.row().classes("w-full justify-between mt-2"):
                    def go_signup():
                        state["auth_view"] = "signup"
                        render_page_body()

                    def go_forgot():
                        state["auth_view"] = "forgot"
                        render_page_body()

                    ui.link("Sign Up", "#").on("click", go_signup).classes("text-sm")
                    ui.link("Forgot Username/Password?", "#").on("click", go_forgot).classes("text-sm")

            with ui.tab_panel(department_tab):
                def on_dept_inst(e):
                    state["login_dept_institute_name"] = e.value

                def on_dept_user(e):
                    state["login_dept_username"] = e.value

                def on_dept_pass(e):
                    state["login_dept_password"] = e.value

                ui.input(label="Institute Name", value=state["login_dept_institute_name"],
                          on_change=on_dept_inst).classes("w-full").props("outlined dense")
                ui.input(label="Department Username", value=state["login_dept_username"],
                          on_change=on_dept_user).classes("w-full mt-2").props("outlined dense")
                ui.input(label="Department Password", value=state["login_dept_password"], password=True,
                          on_change=on_dept_pass).classes("w-full mt-2").props("outlined dense")

                def do_department_login():
                    res, err = mt.authenticate_department(
                        state["login_dept_institute_name"], state["login_dept_username"],
                        state["login_dept_password"],
                    )
                    if res is None:
                        ui.notify(err, type="negative")
                        return
                    state["logged_in"] = {"type": "department", **res}
                    state["mode"] = "seating"
                    state["active_scheme"] = None
                    state["scheme_group_called"] = False
                    state["seating_paste_year"] = ""
                    state["seating_manual_year"] = ""
                    state["seating_columns"] = {k: "" for k, _ in SEATING_COLUMN_SPECS}
                    state["seating_parsed_rows"] = None
                    reset_all_operational_modes()
                    ui.navigate.reload()

                ui.button("Login", icon="login", on_click=do_department_login).classes("w-full mt-3").props(
                    "unelevated color=primary"
                )
                ui.label(
                    "Forgotten department credentials? Ask your institute's admin -- they can "
                    "look them up under Generate Departments."
                ).classes("text-xs text-gray-500 mt-2")

        def on_tab_change(e):
            state["login_type"] = "institute" if e.value == institute_tab else "department"

        tabs.on_value_change(on_tab_change)


def render_signup_screen():
    ui.label("Institute Sign Up").classes("text-2xl font-bold mt-8")
    with ui.card().classes("w-96 mt-4"):
        def on_name(e):
            state["signup_institute_name"] = e.value

        def on_user(e):
            state["signup_username"] = e.value

        def on_pass(e):
            state["signup_password"] = e.value

        def on_email(e):
            state["signup_recovery_email"] = e.value

        ui.input(label="Institute Name", value=state["signup_institute_name"],
                  on_change=on_name).classes("w-full").props("outlined dense")
        ui.input(label="Username (email)", value=state["signup_username"],
                  on_change=on_user).classes("w-full mt-2").props("outlined dense")
        ui.input(label="Password", value=state["signup_password"], password=True,
                  on_change=on_pass).classes("w-full mt-2").props("outlined dense")
        ui.input(label="Recovery Email", value=state["signup_recovery_email"],
                  on_change=on_email).classes("w-full mt-2").props("outlined dense")
        ui.label(
            "The recovery email is only used if you forget your username or password -- "
            "make sure it is typed correctly."
        ).classes("text-xs text-gray-500 mt-2")

        def do_signup():
            name = state["signup_institute_name"].strip()
            username = state["signup_username"].strip()
            password = state["signup_password"]
            email = state["signup_recovery_email"].strip()
            if not name or not username or not password or not email:
                ui.notify("Fill in every field first.", type="warning")
                return
            if "@" not in email or "." not in email.split("@")[-1]:
                ui.notify("Enter a valid recovery email address.", type="warning")
                return
            ok, err = mt.sign_up_institute(name, username, password, email)
            if not ok:
                ui.notify(err, type="negative")
                return
            state["auth_view"] = "login"
            state["login_institute_username"] = username
            ui.notify("Account created -- you can log in now.", type="positive")
            render_page_body()

        ui.button("Sign Up", icon="how_to_reg", on_click=do_signup).classes("w-full mt-3").props(
            "unelevated color=primary"
        )

        def back_to_login():
            state["auth_view"] = "login"
            render_page_body()

        ui.link("Back to Login", "#").on("click", back_to_login).classes("text-sm mt-2")


def render_forgot_screen():
    ui.label("Forgot Username/Password").classes("text-2xl font-bold mt-8")
    with ui.card().classes("w-96 mt-4"):
        def on_email(e):
            state["forgot_recovery_email"] = e.value

        ui.input(label="Recovery Email", value=state["forgot_recovery_email"],
                  on_change=on_email).classes("w-full").props("outlined dense")
        ui.label(
            "If an account with this recovery email exists, its username and password "
            "will be emailed to this address."
        ).classes("text-xs text-gray-500 mt-2")

        def do_forgot():
            ok, err = mt.forgot_institute_credentials(state["forgot_recovery_email"].strip())
            if not ok:
                ui.notify(err, type="negative")
                return
            ui.notify("Check your email for your account details.", type="positive")
            state["auth_view"] = "login"
            render_page_body()

        ui.button("Send", icon="email", on_click=do_forgot).classes("w-full mt-3").props(
            "unelevated color=primary"
        )

        def back_to_login():
            state["auth_view"] = "login"
            render_page_body()

        ui.link("Back to Login", "#").on("click", back_to_login).classes("text-sm mt-2")


def render_institute_dashboard():
    inst = state["logged_in"]

    with ui.row().classes("w-full items-center justify-between"):
        ui.label(f"Institute Dashboard -- {inst['institute_name']}").classes("text-xl font-bold")

        def do_logout():
            state["logged_in"] = None
            state["active_scheme"] = None
            state["scheme_group_called"] = False
            ui.navigate.reload()

        ui.button("Logout", icon="logout", on_click=do_logout).props("outline")

    with ui.row().classes("w-full no-wrap items-start gap-4 mt-4"):
        # ---------------- LEFT SIDEBAR ----------------
        with ui.column().classes("w-56 gap-2 flex-shrink-0"):
            ui.label("Seating Chart").classes("text-xs uppercase text-gray-500 tracking-wide")

            def open_institute_seating_chart():
                state["institute_view"] = "seating_chart"
                render_page_body()

            ui.button(
                "Institute Seating Chart", icon="event_seat", on_click=open_institute_seating_chart,
            ).props("align=left unelevated").classes("w-full justify-start")

            def open_x_table():
                state["institute_view"] = "x_table"
                state["x_table_program"] = None
                state["x_table_institute_overview"] = False
                state["xt_filter_confirmed"] = False
                render_page_body()

            ui.button(
                "X Table", icon="grid_on", on_click=open_x_table,
            ).props("align=left unelevated").classes("w-full justify-start")

        # ---------------- RIGHT CONTENT ----------------
        with ui.column().classes("flex-grow gap-4 min-w-0"):
            view = state["institute_view"]
            if view == "seating_chart":
                render_institute_seating_chart_screen()
            elif view == "seating_chart_adddel":
                render_institute_seating_adddel_screen()
            elif view == "x_table":
                render_x_table_screen()
            elif view == "practical_timetable":
                render_practical_timetable_screen()
            elif view == "online_theory":
                render_online_theory_screen()
            else:
                render_institute_dashboard_tiles()


def render_institute_dashboard_tiles():
    """The dashboard's own tiles (Generate Departments + the two
    placeholder timetable tiles). Institute Seating Chart / X Table are
    NOT tiles here -- they live in the left sidebar (see
    render_institute_dashboard()), not on this tile grid.
    """
    inst = state["logged_in"]
    with ui.row().classes("w-full gap-4 items-start flex-wrap"):
        # ---------------- TILE 1: Generate Departments ----------------
        with ui.card().classes("w-96"):
            ui.label("Generate Departments").classes("text-lg font-bold")

            def on_count_change(e):
                raw = (e.value or "").strip()
                try:
                    n = max(0, min(50, int(raw)))
                except ValueError:
                    n = 0
                state["gen_dept_count"] = raw
                fields = state["gen_dept_fields"]
                if n > len(fields):
                    fields.extend([{"name": "", "username": "", "password": ""} for _ in range(n - len(fields))])
                else:
                    del fields[n:]
                render_page_body()

            ui.input(label="Number of departments", value=state["gen_dept_count"],
                      on_change=on_count_change).classes("w-full").props("outlined dense")

            fields = state["gen_dept_fields"]
            for i in range(len(fields)):
                with ui.card().classes("w-full mt-2 bg-gray-50"):
                    ui.label(f"Department {i + 1}").classes("text-sm font-semibold")

                    def on_field_change(e, idx=i, key="name"):
                        state["gen_dept_fields"][idx][key] = e.value

                    ui.input(label="Name of Department", value=fields[i]["name"],
                              on_change=lambda e, idx=i: on_field_change(e, idx, "name")).classes(
                        "w-full mt-1"
                    ).props("outlined dense")
                    ui.input(label="Create Username", value=fields[i]["username"],
                              on_change=lambda e, idx=i: on_field_change(e, idx, "username")).classes(
                        "w-full mt-1"
                    ).props("outlined dense")
                    ui.input(label="Create Password (4-digit PIN)", value=fields[i]["password"],
                              on_change=lambda e, idx=i: on_field_change(e, idx, "password")).classes(
                        "w-full mt-1"
                    ).props("outlined dense maxlength=4")

            if fields:
                def save_departments():
                    for f in state["gen_dept_fields"]:
                        name = f["name"].strip()
                        username = f["username"].strip()
                        password = f["password"].strip()
                        if not name or not username or not password:
                            ui.notify("Fill in every department's fields first.", type="warning")
                            return
                    created, errors = 0, []
                    for f in state["gen_dept_fields"]:
                        ok, err = mt.create_department(
                            inst["id"], f["name"].strip(), f["username"].strip(), f["password"].strip(),
                        )
                        if ok:
                            created += 1
                        else:
                            errors.append(f"{f['name']}: {err}")
                    state["gen_dept_count"] = ""
                    state["gen_dept_fields"] = []
                    if errors:
                        ui.notify(f"Saved {created}, but {len(errors)} failed: {'; '.join(errors)}", type="warning")
                    else:
                        ui.notify(f"Saved {created} department(s).", type="positive")
                    render_page_body()

                ui.button("Save", icon="save", on_click=save_departments).classes("w-full mt-3").props(
                    "unelevated color=primary"
                )

            existing = mt.list_departments_for_institute(inst["id"])
            if existing:
                ui.separator().classes("my-3")
                ui.label("Existing departments:").classes("text-sm font-semibold")
                for d in existing:
                    if state["editing_department_id"] == d["id"]:
                        with ui.card().classes("w-full mt-2 bg-blue-50"):
                            def on_edit_name(e):
                                state["edit_dept_name"] = e.value

                            def on_edit_username(e):
                                state["edit_dept_username"] = e.value

                            def on_edit_password(e):
                                state["edit_dept_password"] = e.value

                            ui.input(label="Name of Department", value=state["edit_dept_name"],
                                      on_change=on_edit_name).classes("w-full").props("outlined dense")
                            ui.input(label="Username", value=state["edit_dept_username"],
                                      on_change=on_edit_username).classes("w-full mt-1").props("outlined dense")
                            ui.input(label="Password (4-digit PIN)", value=state["edit_dept_password"],
                                      on_change=on_edit_password).classes("w-full mt-1").props(
                                "outlined dense maxlength=4"
                            )

                            def save_edit(dept_id=d["id"]):
                                name = state["edit_dept_name"].strip()
                                username = state["edit_dept_username"].strip()
                                password = state["edit_dept_password"].strip()
                                if not name or not username or not password:
                                    ui.notify("Fill in every field first.", type="warning")
                                    return
                                ok, err = mt.update_department(dept_id, name, username, password)
                                if not ok:
                                    ui.notify(err, type="negative")
                                    return
                                state["editing_department_id"] = None
                                ui.notify("Department updated.", type="positive")
                                render_page_body()

                            def cancel_edit():
                                state["editing_department_id"] = None
                                render_page_body()

                            with ui.row().classes("gap-2 mt-2"):
                                ui.button("Save", icon="save", on_click=save_edit).props(
                                    "unelevated color=primary dense"
                                )
                                ui.button("Cancel", on_click=cancel_edit).props("outline dense")
                    else:
                        with ui.row().classes("w-full items-center justify-between mt-1"):
                            ui.label(
                                f"{d['department_name']} -- username: {d['username']}, password: {d['password']}"
                            ).classes("text-xs text-gray-600")

                            def start_edit(dept=d):
                                state["editing_department_id"] = dept["id"]
                                state["edit_dept_name"] = dept["department_name"]
                                state["edit_dept_username"] = dept["username"]
                                state["edit_dept_password"] = dept["password"]
                                render_page_body()

                            def ask_delete(dept=d):
                                with ui.dialog() as dialog, ui.card():
                                    ui.label(f"Delete department '{dept['department_name']}'?").classes(
                                        "text-md font-bold text-red-700"
                                    )
                                    ui.label(
                                        "This removes the department's LOGIN ONLY -- it will no longer "
                                        "be able to sign in. Any data it has already created (scheme "
                                        "databases, layout_mapping.json, reports, seating chart) stays "
                                        "on disk untouched. This cannot be undone from here."
                                    ).classes("text-sm mt-1")

                                    def do_delete(dept_id=dept["id"]):
                                        dialog.close()
                                        mt.delete_department(dept_id)
                                        ui.notify("Department login deleted.", type="warning")
                                        render_page_body()

                                    with ui.row().classes("w-full justify-end gap-2 mt-3"):
                                        ui.button("Cancel", on_click=dialog.close).props("outline")
                                        ui.button("Yes, Delete", color="negative", on_click=do_delete)
                                dialog.open()

                            with ui.row().classes("gap-1"):
                                ui.button(icon="edit", on_click=start_edit).props("flat dense round size=sm")
                                ui.button(icon="delete", on_click=ask_delete).props(
                                    "flat dense round size=sm color=negative"
                                )

        # ---------------- TILE 2: Practical Time Table ----------------
        with ui.card().classes("w-72"):
            ui.label("Generate Practical Time Table").classes("text-lg font-bold")
            ui.label("For all departments.").classes("text-xs text-gray-500 mt-1")

            def open_practical_timetable():
                state["institute_view"] = "practical_timetable"
                render_page_body()

            ui.button("Generate", icon="event_note", on_click=open_practical_timetable).props("outline").classes("mt-3")

        # ---------------- TILE 3: Online Theory Time Table ----------------
        with ui.card().classes("w-72"):
            ui.label("Online Theory Time Table").classes("text-lg font-bold")
            ui.label("For all departments.").classes("text-xs text-gray-500 mt-1")

            def open_online_theory():
                state["institute_view"] = "online_theory"
                render_page_body()

            ui.button("Generate", icon="schedule", on_click=open_online_theory).props("outline").classes("mt-3")


def _ott_reset_draft():
    state["ott_programs"] = []
    state["ott_semesters"] = []
    state["ott_l1"], state["ott_l2"] = [], []
    state["ott_filter_confirmed"] = False
    state["ott_selected"] = set()
    state["ott_max"] = {}
    state["ott_times"] = {}


def render_online_theory_screen():
    """Tile 3 -- "Online Theory Time Table". Reads only the Institute Seating Chart of the chosen
    Year/Session. A saved table (if any) is shown unchanged; the set-up form appears when there is none or
    when the user chooses to edit/regenerate."""
    inst = state["logged_in"]
    inst_name = inst["institute_name"]
    with ui.row().classes("w-full items-center justify-between"):
        ui.label("Online Theory Time Table").classes("text-xl font-bold")

        def back_to_dashboard():
            state["institute_view"] = "dashboard"
            render_page_body()

        ui.button("Back to Dashboard", icon="arrow_back", on_click=back_to_dashboard).props("outline")

    dbs = mt.list_institute_seating_chart_dbs(inst_name)
    if not dbs:
        with ui.card().classes("w-full mt-3"):
            ui.icon("warning", color="warning").classes("text-3xl")
            ui.label("Load institute seating chart first").classes("text-md font-semibold text-red-600 mt-1")
            ui.label("No Institute Seating Chart database has been saved yet for this institute.").classes(
                "text-xs text-gray-500 mt-1"
            )
        return

    if not state["ott_db_confirmed"]:
        with ui.card().classes("w-full mt-3"):
            ui.label("Select Institute Seating Chart database").classes("text-md font-semibold")
            with ui.row().classes("w-full gap-2 mt-2 flex-wrap"):
                for entry in dbs:
                    def pick_db(e=entry):
                        state["ott_year"], state["ott_session"] = e["year"], e["session"]
                        state["ott_db_confirmed"] = True
                        state["ott_saved_key"] = None
                        render_page_body()

                    ui.button(f"{entry['year']} / {entry['session']}", icon="folder_open", on_click=pick_db).props(
                        "outline dense"
                    )
        return

    year, session = state["ott_year"], state["ott_session"]
    with ui.row().classes("items-center gap-3"):
        ui.label(f"{year} / {session}").classes("text-sm text-gray-600")

        def change_db():
            state["ott_db_confirmed"] = False
            state["ott_saved_key"] = None
            render_page_body()

        ui.button("Change database", icon="swap_horiz", on_click=change_db).props("flat dense")

    key = (inst_name, year, session)
    if state["ott_saved_key"] != key:
        state["ott_saved"] = mt.load_online_timetable(inst_name, year, session)
        state["ott_saved_key"] = key
        state["ott_edit_mode"] = False
        _ott_reset_draft()

    if state["ott_saved"] and not state["ott_edit_mode"]:
        render_online_theory_saved(inst_name, year, session)
    else:
        render_online_theory_form(inst_name, year, session)


def render_online_theory_saved(inst_name, year, session):
    saved = state["ott_saved"]
    cfg = mt.normalize_online_config(saved["config"])
    rows, warnings = saved["rows"], saved["warnings"]
    shown = [{k: v for k, v in r.items() if k != "members"} for r in rows]

    with ui.card().classes("w-full mt-3"):
        ui.label(
            f"Program Code(s): {', '.join(cfg['program_codes'])}   |   "
            f"Semester(s): {', '.join(s.title() for s in cfg['semester_labels'])}   |   "
            f"Level 1: {', '.join(cfg['level1'])}   |   Level 2: {', '.join(cfg['level2'])}"
        ).classes("text-sm font-semibold")
        ui.label(
            f"Saved time table -- generated on {_fmt_generated_at(saved['generated_at'])}. It stays exactly as "
            "generated until you edit and generate it again."
        ).classes("text-xs text-gray-600 mt-1")
        if mt.compute_timetable_signature(inst_name, year, session, "online") != saved["signature"]:
            with ui.row().classes("items-center gap-2 mt-1 bg-orange-50 border border-orange-300 rounded px-2 py-1"):
                ui.icon("warning", color="warning").classes("text-sm")
                ui.label("Data changed since this was generated -- click Edit / Regenerate to update").classes(
                    "text-xs font-semibold text-orange-700"
                )

        def download_pdf():
            path = mt.generate_online_timetable_pdf(rows, warnings, inst_name, year, session, cfg)
            ui.download(path, os.path.basename(path))

        def start_edit():
            state["ott_programs"] = list(cfg["program_codes"])
            state["ott_semesters"] = list(cfg["semester_labels"])
            state["ott_l1"], state["ott_l2"] = list(cfg["level1"]), list(cfg["level2"])
            state["ott_filter_confirmed"] = True
            _k = lambda s: (s["program_code"], s["semester_label"], s["scheme"], s["subject"])
            state["ott_selected"] = {_k(s) for s in cfg["subjects"]}
            state["ott_max"] = {_k(s): str(s["max_per_batch"]) for s in cfg["subjects"]}
            state["ott_times"] = {
                _k(s) + (i,): dict(tm) for s in cfg["subjects"] for i, tm in enumerate(s.get("times") or [])
            }
            state["ott_edit_mode"] = True
            render_page_body()

        def ask_delete():
            def go():
                mt.delete_online_timetable(inst_name, year, session)
                state["ott_saved"] = None
                _ott_reset_draft()
                ui.notify("Saved time table deleted.", type="warning")
                render_page_body()

            _confirm_dialog("Delete the saved time table?", "The saved Online Theory Time Table is removed.",
                            go, "Yes, delete")

        with ui.row().classes("gap-2 mt-2"):
            ui.button("Download PDF", icon="picture_as_pdf", on_click=download_pdf).props("unelevated color=primary")
            ui.button("Edit / Regenerate", icon="edit", on_click=start_edit).props("outline")
            ui.button("Delete saved time table", icon="delete", on_click=ask_delete).props("outline color=negative")

    columns = [
        {"name": "sr_no", "label": "Sr.No", "field": "sr_no", "align": "left"},
        {"name": "date", "label": "Date", "field": "date", "align": "left"},
        {"name": "day", "label": "Day", "field": "day", "align": "left"},
        {"name": "time", "label": "Time", "field": "time", "align": "left"},
        {"name": "compact_code", "label": "Program/Sem/Scheme", "field": "compact_code", "align": "left"},
        {"name": "subject", "label": "Subject", "field": "subject", "align": "left"},
        {"name": "levels", "label": "Levels", "field": "levels", "align": "left"},
        {"name": "subject_total", "label": "Total (subject)", "field": "subject_total", "align": "center"},
        {"name": "batch_label", "label": "Batch", "field": "batch_label", "align": "left"},
        {"name": "seat_range", "label": "Seat No. Range", "field": "seat_range", "align": "left"},
        {"name": "num_students", "label": "No. of Students", "field": "num_students", "align": "center"},
        {"name": "categories", "label": "Category-wise", "field": "categories", "align": "left"},
    ]
    with ui.card().classes("w-full mt-3"):
        ui.table(columns=columns, rows=shown, row_key="sr_no").classes("w-full").props("dense flat bordered")

    with ui.card().classes("w-full mt-3 " + ("border-2 border-orange-300" if warnings else "")):
        if warnings:
            ui.label(f"Warnings ({len(warnings)}) -- information only, nothing was changed").classes(
                "text-sm font-semibold text-orange-700"
            )
            with ui.column().classes("gap-0 mt-1 max-h-64 overflow-y-auto"):
                for w in warnings:
                    ui.label(w).classes("text-xs text-orange-700")
        else:
            ui.label("No warnings -- no student has overlapping exams and every student is in a batch.").classes(
                "text-sm text-green-700"
            )


def render_online_theory_form(inst_name, year, session):
    saved = state["ott_saved"]
    with ui.card().classes("w-full mt-3"):
        ui.label("Online Theory Time Table -- set up").classes("text-md font-semibold")
        if saved:
            ui.label(
                "You are editing the saved time table. Generating again will REPLACE it (you will be asked to confirm)."
            ).classes("text-xs text-orange-600")

            def cancel_edit():
                state["ott_edit_mode"] = False
                _ott_reset_draft()
                render_page_body()

            ui.button("Cancel editing", icon="close", on_click=cancel_edit).props("outline dense").classes("mt-1")
        ui.label(
            "Choose one or more Program Codes and Semesters, then the Level 1 / Level 2 entries that count as the "
            "online theory paper (e.g. TH and SA), and click Continue. Only matching Subject-Level1-Level2 entries "
            "are counted; every subject is taken exactly as the seating chart lists it. Program codes, semesters "
            "and schemes are never mixed in one count."
        ).classes("text-xs text-gray-500 mt-1")

        program_codes = mt.get_institute_seating_chart_program_codes(inst_name, year, session)
        present_sems = set()
        for pc in program_codes:
            present_sems |= {r["semester_label"] for r in
                             mt.get_institute_seating_chart_for_program(inst_name, year, session, pc)}
        sem_options = [s for s in mt.SEMESTER_NAMES if s in present_sems]
        l1_opts, l2_opts = mt.get_all_level1_level2(inst_name, year, session)

        def on_programs(e):
            # Only record the pending choice -- no re-render, so picking several options doesn't close the list.
            state["ott_programs"] = e.value or []
            state["ott_filter_confirmed"] = False

        def on_semesters(e):
            state["ott_semesters"] = e.value or []
            state["ott_filter_confirmed"] = False

        def on_l1(e):
            state["ott_l1"] = e.value or []
            state["ott_filter_confirmed"] = False

        def on_l2(e):
            state["ott_l2"] = e.value or []
            state["ott_filter_confirmed"] = False

        with ui.row().classes("w-full gap-3 mt-2"):
            ui.select(program_codes, label="Program Code(s)",
                      value=[x for x in state["ott_programs"] if x in program_codes], multiple=True,
                      on_change=on_programs).classes("flex-1").props("outlined dense use-chips")
            ui.select(sem_options, label="Semester(s)",
                      value=[x for x in state["ott_semesters"] if x in sem_options], multiple=True,
                      on_change=on_semesters).classes("flex-1").props("outlined dense use-chips")
        with ui.row().classes("w-full gap-3 mt-2"):
            ui.select(l1_opts, label="Level 1", value=[x for x in state["ott_l1"] if x in l1_opts], multiple=True,
                      on_change=on_l1).classes("flex-1").props("outlined dense use-chips")
            ui.select(l2_opts, label="Level 2", value=[x for x in state["ott_l2"] if x in l2_opts], multiple=True,
                      on_change=on_l2).classes("flex-1").props("outlined dense use-chips")

        def confirm_filter():
            if not state["ott_programs"] or not state["ott_semesters"]:
                ui.notify("Choose at least one Program Code and one Semester first.", type="warning")
                return
            if not state["ott_l1"] or not state["ott_l2"]:
                ui.notify("Select at least one Level 1 and one Level 2 option.", type="warning")
                return
            state["ott_filter_confirmed"] = True
            render_page_body()

        with ui.row().classes("items-center gap-2 mt-2"):
            ui.button("Continue", icon="arrow_forward", on_click=confirm_filter).props("unelevated color=primary")
            if state["ott_filter_confirmed"]:
                ui.icon("check_circle", color="positive").classes("text-sm")
                ui.label("Selection applied.").classes("text-xs text-green-700")
            elif state["ott_programs"] or state["ott_semesters"] or state["ott_l1"] or state["ott_l2"]:
                ui.label("Selections pending -- click Continue to apply.").classes("text-xs text-orange-600")

    if not state["ott_filter_confirmed"]:
        return

    subjects = mt.get_online_theory_subjects(
        inst_name, year, session, state["ott_programs"], state["ott_semesters"], state["ott_l1"], state["ott_l2"],
    )
    if not subjects:
        with ui.card().classes("w-full mt-3"):
            ui.label("No subject matches those Program Codes / Semesters / Level filters.").classes(
                "text-sm text-orange-600")
        return

    def skey(s):
        return (s["program_code"], s["semester_label"], s["scheme"], s["subject"])

    # ---------------- Tick subjects (program code / semester / scheme kept separate) ----------------
    with ui.card().classes("w-full mt-3"):
        ui.label("Subjects -- tick the ones to put in the time table").classes("text-md font-semibold")
        seen_groups = []
        for s in subjects:
            g = (s["program_code"], s["semester_label"], s["scheme"])
            if g not in seen_groups:
                seen_groups.append(g)
        for g in seen_groups:
            ui.label(f"{g[0]} / {g[1].title()} / Scheme {g[2]}").classes("text-sm font-semibold text-gray-600 mt-2")
            for s in [x for x in subjects if (x["program_code"], x["semester_label"], x["scheme"]) == g]:
                k = skey(s)

                def on_tick(e, kk=k):
                    if e.value:
                        state["ott_selected"].add(kk)
                    else:
                        state["ott_selected"].discard(kk)
                    render_page_body()
                    restore_scroll_positions()

                cats = ", ".join(f"{c} {n}" for c, n in s["category_counts"].items())
                ui.checkbox(
                    f"{s['subject']}  --  {s['total']} student(s)  ({cats})  [{', '.join(s['levels'])}]",
                    value=k in state["ott_selected"], on_change=on_tick,
                ).classes("text-sm")

    chosen = [s for s in subjects if skey(s) in state["ott_selected"]]
    state["ott_selected"] = {skey(s) for s in chosen}  # drop ticks no longer in the list
    if not chosen:
        return

    # ---------------- Per subject: max per batch -> batches -> date / time ----------------
    for s in chosen:
        k = skey(s)
        with ui.card().classes("w-full mt-3"):
            ui.label(
                f"{s['program_code']} / {s['semester_label'].title()} / {s['subject']} (Scheme {s['scheme']}) "
                f"-- {s['total']} student(s) in total"
            ).classes("text-sm font-bold")
            ui.label("Category-wise: " + ", ".join(f"{c} {n}" for c, n in s["category_counts"].items())).classes(
                "text-xs text-gray-600")

            def on_max(e, kk=k):
                state["ott_max"][kk] = e.value or ""

            def apply_max():
                render_page_body()
                restore_scroll_positions()

            inp = ui.input(
                label="Maximum students per batch", value=state["ott_max"].get(k, ""), on_change=on_max,
            ).props("dense outlined type=number").classes("w-64 mt-1")
            inp.on("blur", apply_max)
            inp.on("keydown.enter", apply_max)

            try:
                max_per = int(str(state["ott_max"].get(k, "")).strip())
            except ValueError:
                max_per = 0
            if max_per < 1:
                ui.label("Enter the maximum students per batch (and press Enter) to create the batches.").classes(
                    "text-xs text-gray-500 mt-1")
                continue

            batches, non_numeric = mt.compute_online_batches(s["students"], max_per)
            if non_numeric:
                ui.label(
                    f"{len(non_numeric)} student(s) have no numeric seat number and are NOT in any batch: "
                    + ", ".join(f"{x['enrollment']} (seat \"{x['seat_number']}\")" for x in non_numeric[:6])
                    + (" ..." if len(non_numeric) > 6 else "")
                ).classes("text-xs text-orange-700 mt-1")
            ui.label(f"{len(batches)} batch(es)").classes("text-xs font-semibold mt-1")
            with ui.row().classes("gap-2 font-semibold text-xs border-b pb-1 mt-1"):
                ui.label("Batch").classes("w-14")
                ui.label("Seat No. Range").classes("w-40")
                ui.label("Students").classes("w-20")
                ui.label("Category-wise").classes("w-40")
                ui.label("Date").classes("w-40")
                ui.label("Start").classes("w-32")
                ui.label("End").classes("w-32")
            for b in batches:
                tk = k + (b["batch_index"],)
                tm = state["ott_times"].setdefault(tk, {"date": "", "start": "", "end": ""})

                def on_time(e, t_, field):
                    t_[field] = e.value or ""

                with ui.row().classes("gap-2 items-center py-1 border-b"):
                    ui.label(f"B{b['batch_index'] + 1}").classes("w-14 font-semibold")
                    ui.label(f"{b['start_seat']}-{b['end_seat']}").classes("w-40")
                    ui.label(str(b["total"])).classes("w-20")
                    ui.label(mt._fmt_category_counts(b["category_counts"])).classes("w-40 text-xs")
                    ui.input(value=tm["date"], on_change=lambda e, t_=tm: on_time(e, t_, "date")).props(
                        "dense outlined type=date").classes("w-40")
                    ui.input(value=tm["start"], on_change=lambda e, t_=tm: on_time(e, t_, "start")).props(
                        "dense outlined type=time").classes("w-32")
                    ui.input(value=tm["end"], on_change=lambda e, t_=tm: on_time(e, t_, "end")).props(
                        "dense outlined type=time").classes("w-32")

    # ---------------- Generate & save ----------------
    def build_config():
        out = []
        for s in chosen:
            k = skey(s)
            try:
                max_per = int(str(state["ott_max"].get(k, "")).strip())
            except ValueError:
                max_per = 0
            n = len(mt.compute_online_batches(s["students"], max_per)[0]) if max_per >= 1 else 0
            out.append({
                "program_code": s["program_code"], "semester_label": s["semester_label"],
                "scheme": s["scheme"], "subject": s["subject"], "max_per_batch": state["ott_max"].get(k, ""),
                "times": [dict(state["ott_times"].get(k + (i,), {})) for i in range(n)],
            })
        return {
            "program_codes": list(state["ott_programs"]), "semester_labels": list(state["ott_semesters"]),
            "level1": list(state["ott_l1"]), "level2": list(state["ott_l2"]), "subjects": out,
        }

    def do_generate():
        cfg = build_config()
        rows, warnings, errors = mt.build_online_timetable_rows(inst_name, year, session, cfg)
        if errors:
            ui.notify("Cannot save yet: " + " | ".join(errors[:6]) + (" ..." if len(errors) > 6 else ""),
                      type="negative", multi_line=True)
            return
        mt.save_online_timetable(inst_name, year, session, cfg, rows, warnings)
        state["ott_saved"] = mt.load_online_timetable(inst_name, year, session)
        state["ott_edit_mode"] = False
        ui.notify(
            f"Time table saved ({len(rows)} batch row(s))" + (f" with {len(warnings)} warning(s)." if warnings else "."),
            type="warning" if warnings else "positive",
        )
        render_page_body()

    def generate():
        if state["ott_saved"]:
            _confirm_dialog(
                "Replace the saved time table?",
                "A time table was saved earlier. Generating again REPLACES it with the one built from the "
                "settings above.", do_generate, "Yes, replace",
            )
        else:
            do_generate()

    with ui.card().classes("w-full mt-3"):
        ui.button("Generate & Save Time Table", icon="save", on_click=generate).props("unelevated color=primary")
        ui.label(
            "Every ticked subject needs a maximum per batch, and every batch needs a date, start time and end "
            "time (end after start)."
        ).classes("text-xs text-gray-500 mt-1")


def render_practical_timetable_screen():
    """Tile 2 -- "Generate Practical Time Table". Phase F: the database
    gate ("Load institute seating chart first" if none exist) and the
    global Year+Session picker now live HERE, at the shell level --
    selected once, before any mode is even shown. All three modes
    (Pre-requisites, Subject/Workshop/Faculty Mapping, Practical Time
    Table) read from this one shared selection; none of them has its
    own database picker anymore.
    """
    inst = state["logged_in"]
    with ui.row().classes("w-full items-center justify-between"):
        ui.label("Generate Practical Time Table").classes("text-xl font-bold")

        def back_to_dashboard():
            state["institute_view"] = "dashboard"
            render_page_body()

        ui.button("Back to Dashboard", icon="arrow_back", on_click=back_to_dashboard).props("outline")

    existing_dbs = mt.list_institute_seating_chart_dbs(inst["institute_name"])
    if not existing_dbs:
        with ui.card().classes("w-full mt-3"):
            ui.icon("warning", color="warning").classes("text-3xl")
            ui.label("Load institute seating chart first").classes("text-md font-semibold text-red-600 mt-1")
            ui.label(
                "No Institute Seating Chart database has been saved yet for this institute -- "
                "every mode here needs at least one before it can do anything."
            ).classes("text-xs text-gray-500 mt-1")
        return

    if not state["ptt_db_confirmed"]:
        with ui.card().classes("w-full mt-3"):
            ui.label("Select Institute Seating Chart database").classes("text-md font-semibold")
            ui.label(
                "Selected once here -- every mode below reads from this same database."
            ).classes("text-xs text-gray-500")
            with ui.row().classes("w-full gap-2 mt-2 flex-wrap"):
                for entry in existing_dbs:
                    def pick_db(e=entry):
                        state["ptt_year"] = e["year"]
                        state["ptt_session"] = e["session"]
                        state["ptt_db_confirmed"] = True
                        state["ptt_active_button"] = None
                        render_page_body()

                    ui.button(
                        f"{entry['year']} / {entry['session']}", icon="folder_open", on_click=pick_db,
                    ).props("outline dense")
        return

    with ui.row().classes("w-full no-wrap items-start gap-4 mt-4"):
        # ---------------- MODE SIDE PANEL ----------------
        with ui.column().classes("w-56 gap-2 flex-shrink-0"):
            ui.label(f"{state['ptt_year']} / {state['ptt_session']}").classes(
                "text-xs text-gray-500"
            )

            def change_database():
                state["ptt_db_confirmed"] = False
                state["ptt_active_button"] = None
                render_page_body()

            ui.button("Change database", icon="swap_horiz", on_click=change_database).props(
                "flat dense"
            ).classes("w-full justify-start text-xs")

            ui.label("Modes").classes("text-xs uppercase text-gray-500 tracking-wide mt-2")

            def make_mode_button(mode_id, label, icon):
                def open_mode():
                    state["ptt_mode"] = mode_id
                    render_page_body()

                is_active = state["ptt_mode"] == mode_id
                ui.button(
                    label, icon=icon, on_click=open_mode,
                ).props(f"align=left {'unelevated color=primary' if is_active else 'outline'}").classes(
                    "w-full justify-start"
                )

            make_mode_button("prerequisites", "Pre-requisites", "checklist")
            make_mode_button("schedule", "Practical Time Table", "event_note")

        # ---------------- MODE CONTENT ----------------
        with ui.column().classes("flex-grow gap-4 min-w-0"):
            if state["ptt_mode"] == "prerequisites":
                render_prerequisites_mode()
            elif state["ptt_mode"] == "schedule":
                render_schedule_mode()


def _confirm_dialog(title, text, on_yes, yes_label="Yes"):
    """Small Yes/Cancel dialog; on_yes may be a plain or an async function."""
    with ui.dialog() as dialog, ui.card():
        ui.label(title).classes("text-md font-bold")
        ui.label(text).classes("text-sm mt-1")

        async def yes():
            dialog.close()
            result = on_yes()
            if asyncio.iscoroutine(result):
                await result

        with ui.row().classes("gap-2 mt-3 justify-end w-full"):
            ui.button("Cancel", on_click=dialog.close).props("outline")
            ui.button(yes_label, on_click=yes).props("unelevated color=primary")
    dialog.open()


def _fmt_generated_at(value):
    try:
        return datetime.datetime.strptime(value, "%Y-%m-%d %H:%M:%S").strftime("%d-%m-%Y %H:%M")
    except (ValueError, TypeError):
        return value


def _render_saved_timetable_banner(inst_name, year, session, mode):
    """"Saved time table, generated on ..." plus the out-of-date notice when the data behind it changed."""
    meta = state["sch4_saved_meta"].get(mode)
    if not meta:
        return
    ui.label(
        f"Saved time table -- generated on {_fmt_generated_at(meta['generated_at'])} "
        f"(Level 1: {', '.join(meta['level1']) or '-'} | Level 2: {', '.join(meta['level2']) or '-'}). "
        "It stays exactly as generated until you click Generate / Refresh."
    ).classes("text-xs text-gray-600 mt-2")
    if mt.compute_timetable_signature(inst_name, year, session, mode) != meta["signature"]:
        with ui.row().classes("items-center gap-2 mt-1 bg-orange-50 border border-orange-300 rounded px-2 py-1"):
            ui.icon("warning", color="warning").classes("text-sm")
            ui.label("Data changed since this was generated -- click Refresh to update").classes(
                "text-xs font-semibold text-orange-700"
            )


def render_semester_date_ranges(inst_name, year, session):
    """The first section of the Practical Time Table mode: a date range per semester. Semesters that share a
    range are saved together as one group and share the same exam days and time slots. A semester with no
    range is left out of everything below. Saved to the database, so it can be reselected/changed on revisit."""
    groups = mt.get_date_range_groups(inst_name, year, session)
    all_sems = mt.get_institute_semesters(inst_name, year, session)
    ranged = {s for g in groups for s in g["semesters"]}

    def after_change():
        # the database's assignments / slot numbering may have changed -- make every screen below reload
        state["fa_loaded_key"] = None
        state["sch4_manual_rows"] = None
        state["sch4_manual_key"] = None
        state["sch4_manual_auto_failures"] = []
        state["assign_last_unassigned"] = []
        state["assign_other_last_unassigned"] = []
        render_page_body()
        restore_scroll_positions()

    def clear_editor():
        state["dr_edit_id"] = None
        state["dr_semesters"] = []
        state["dr_start"] = state["dr_end"] = ""
        state["dr_rows"] = []

    def clear_text(summary):
        by = summary["cleared_by_semester"]
        return ", ".join(f"{s.title()}: {n}" for s, n in sorted(by.items(), key=lambda kv: mt._sem_rank(kv[0])))

    with ui.card().classes("w-full mt-2"):
        ui.label("Semester-wise Date Range").classes("text-sm font-semibold")
        ui.label(
            "Give each semester its exam date range. Semesters that share the same range are set up together "
            "and share the same exam days and time slots. Only the semesters that have a range are used by "
            "everything below. Saved to the database -- reselect semesters or change a range any time."
        ).classes("text-xs text-gray-500")
        if not all_sems:
            ui.label("No semesters found in this Institute Seating Chart.").classes("text-xs text-gray-400 mt-2")
            return

        # ---------------- saved ranges ----------------
        for g in groups:
            exam_days = [d for d in g["dates"] if d["is_exam_day"]]
            n_slots = sum(len(d["sessions"]) for d in exam_days)
            with ui.row().classes("w-full items-center gap-2 border-b py-1 flex-nowrap"):
                ui.label(", ".join(s.title() for s in g["semesters"])).classes("text-sm font-medium flex-1")
                ui.label(
                    f"{mt.format_date_ddmmyyyy(g['start_date'])} to {mt.format_date_ddmmyyyy(g['end_date'])}  --  "
                    f"{len(exam_days)} exam day(s), {n_slots} slot(s)"
                ).classes("text-xs text-gray-600")
                if n_slots == 0:
                    ui.label("no exam slot").classes("text-xs text-orange-600")

                def start_edit(gg=g):
                    state["dr_edit_id"] = gg["group_id"]
                    state["dr_semesters"] = list(gg["semesters"])
                    state["dr_start"], state["dr_end"] = gg["start_date"], gg["end_date"]
                    state["dr_rows"] = [
                        {"date": d["date"], "day": d["day"], "is_exam_day": d["is_exam_day"],
                         "num_sessions": len(d["sessions"]), "sessions": [list(w) for w in d["sessions"]]}
                        for d in gg["dates"]
                    ]
                    render_page_body()

                def ask_delete(gg=g):
                    summary = mt.delete_date_range_group(inst_name, year, session, gg["group_id"], dry_run=True)
                    text = "These semesters will have no date range and be left out of everything below."
                    if summary["cleared_total"]:
                        text += (f" {summary['cleared_total']} existing assignment(s) will be cleared "
                                 f"({clear_text(summary)}). Workshop/Faculty entries and batches are kept.")

                    def go():
                        mt.delete_date_range_group(inst_name, year, session, gg["group_id"])
                        if state["dr_edit_id"] == gg["group_id"]:
                            clear_editor()
                        ui.notify("Date range deleted.", type="warning")
                        after_change()

                    _confirm_dialog(f"Delete the date range of {', '.join(s.title() for s in gg['semesters'])}?",
                                    text, go, "Yes, delete")

                ui.button(icon="edit", on_click=start_edit).props("flat dense round size=sm")
                ui.button(icon="delete", on_click=ask_delete).props("flat dense round size=sm color=negative")

        missing = [s for s in all_sems if s not in ranged]
        if missing:
            ui.label(
                "No date range yet (left out of everything below): " + ", ".join(s.title() for s in missing)
            ).classes("text-xs text-orange-600 mt-2")

        # ---------------- add / edit ----------------
        ui.label("Change this date range" if state["dr_edit_id"] is not None else "Add a date range").classes(
            "text-sm font-semibold mt-3")
        ui.label(
            "Pick the semesters, the Start and End date, click Generate to list the dates, mark the exam days and "
            "their sessions, then Save to Database. A semester picked here is taken out of any other range."
        ).classes("text-xs text-gray-500")

        def on_sems(e):
            state["dr_semesters"] = e.value or []  # no re-render: keeps the list open while picking several

        ui.select(
            all_sems, label="Semesters", value=[s for s in state["dr_semesters"] if s in all_sems], multiple=True,
            on_change=on_sems,
        ).classes("w-full mt-1").props("outlined dense use-chips")

        with ui.row().classes("w-full gap-3 mt-2 items-end"):
            def on_start(e):
                state["dr_start"] = e.value

            def on_end(e):
                state["dr_end"] = e.value

            ui.input(label="Start Date", value=state["dr_start"], on_change=on_start).props(
                "outlined dense type=date").classes("flex-1")
            ui.input(label="End Date", value=state["dr_end"], on_change=on_end).props(
                "outlined dense type=date").classes("flex-1")

            def generate_dates():
                rng = mt.date_range_with_days(state["dr_start"], state["dr_end"])
                if not rng:
                    ui.notify("Pick a valid Start/End date (End must not be before Start).", type="warning")
                    return
                existing = {r["date"]: r for r in state["dr_rows"]}
                state["dr_rows"] = [
                    existing.get(d) or {"date": d, "day": day, "is_exam_day": False, "num_sessions": 0, "sessions": []}
                    for d, day in rng
                ]
                render_page_body()

            ui.button("Generate", icon="event", on_click=generate_dates).props("unelevated color=primary")

        rows = state["dr_rows"]
        if rows:
            with ui.row().classes("w-full gap-2 font-semibold text-xs border-b pb-1 mt-3"):
                ui.label("Date").classes("w-28")
                ui.label("Day").classes("w-24")
                ui.label("Exam?").classes("w-16")
                ui.label("Sessions").classes("w-20")
                ui.label("Session Times").classes("flex-1 min-w-48")
                ui.label("").classes("w-10")

            for row in list(rows):
                with ui.row().classes("w-full gap-2 items-center border-b py-1"):
                    ui.label(row["date"]).classes("w-28")
                    ui.label(row["day"]).classes("w-24")

                    def on_exam(e, r=row):
                        r["is_exam_day"] = e.value

                    ui.checkbox(value=row["is_exam_day"], on_change=on_exam).classes("w-16")

                    def on_num_sessions(e, r=row):
                        try:
                            n = max(0, min(10, int(e.value or 0)))
                        except ValueError:
                            n = 0
                        r["num_sessions"] = n
                        if len(r["sessions"]) < n:
                            r["sessions"] += [["", ""] for _ in range(n - len(r["sessions"]))]
                        else:
                            r["sessions"] = r["sessions"][:n]
                        render_page_body()

                    ui.input(value=str(row["num_sessions"]), on_change=on_num_sessions).classes("w-20").props(
                        "dense outlined type=number")

                    with ui.row().classes("flex-1 min-w-48 gap-2 flex-wrap"):
                        for i in range(row["num_sessions"]):
                            if i >= len(row["sessions"]):
                                row["sessions"].append(["", ""])

                            def on_start_t(e, r=row, idx=i):
                                r["sessions"][idx][0] = e.value

                            def on_end_t(e, r=row, idx=i):
                                r["sessions"][idx][1] = e.value

                            ui.input(value=row["sessions"][i][0], on_change=on_start_t).props(
                                "dense outlined type=time").classes("w-28")
                            ui.input(value=row["sessions"][i][1], on_change=on_end_t).props(
                                "dense outlined type=time").classes("w-28")

                    def drop_row(r=row):
                        state["dr_rows"].remove(r)
                        render_page_body()

                    ui.button(icon="close", on_click=drop_row).props("flat dense round size=sm color=negative").classes(
                        "w-10")

            def copy_first():
                first = state["dr_rows"][0]
                for r in state["dr_rows"][1:]:
                    r["is_exam_day"] = first["is_exam_day"]
                    r["num_sessions"] = first["num_sessions"]
                    r["sessions"] = [list(s) for s in first["sessions"]]
                render_page_body()

            def save_group():
                sems = [s for s in state["dr_semesters"] if s in all_sems]
                if not sems:
                    ui.notify("Pick at least one semester.", type="warning")
                    return
                rng = mt.date_range_with_days(state["dr_start"], state["dr_end"])
                if not rng:
                    ui.notify("Pick a valid Start/End date (End must not be before Start).", type="warning")
                    return
                in_range = {d for d, _day in rng}
                problems, date_rows = [], []
                for r in state["dr_rows"]:
                    if r["date"] not in in_range:
                        problems.append(f"{r['date']} is outside the Start/End date -- click Generate again.")
                        continue
                    sessions = [(s[0], s[1]) for s in r["sessions"] if s[0] and s[1]]
                    if r["is_exam_day"] and not sessions:
                        problems.append(f"{mt.format_date_ddmmyyyy(r['date'])} is an exam day without a complete session.")
                    for st, en in sessions:
                        if en <= st:
                            problems.append(f"{mt.format_date_ddmmyyyy(r['date'])}: a session ends before it starts.")
                    date_rows.append({"date": r["date"], "day": r["day"], "is_exam_day": r["is_exam_day"],
                                      "sessions": sessions})
                if problems:
                    ui.notify(" | ".join(problems[:4]) + (" ..." if len(problems) > 4 else ""),
                              type="negative", multi_line=True)
                    return
                args = (inst_name, year, session, state["dr_edit_id"], sems, state["dr_start"], state["dr_end"], date_rows)
                dry = mt.save_date_range_group(*args, dry_run=True)

                def go():
                    res = mt.save_date_range_group(*args)
                    clear_editor()
                    msg = "Date range saved."
                    if res["cleared_total"]:
                        msg += f" {res['cleared_total']} assignment(s) outside the range were cleared."
                    ui.notify(msg, type="positive")
                    if res["overlap_warnings"]:
                        ui.notify(" | ".join(res["overlap_warnings"][:3]), type="warning", multi_line=True)
                    after_change()

                if dry["cleared_total"]:
                    _confirm_dialog(
                        "Clear assignments outside the new range?",
                        f"{dry['cleared_total']} existing assignment(s) fall outside the new date range(s) and will be "
                        f"cleared ({clear_text(dry)}). Assignments inside the range are kept. Workshop/Faculty "
                        "entries and batches are kept.", go, "Yes, save and clear",
                    )
                else:
                    go()

            with ui.row().classes("gap-2 mt-3"):
                ui.button("Save to Database", icon="save", on_click=save_group).props("unelevated color=primary")
                ui.button("Copy first date's setup to all dates", icon="content_copy", on_click=copy_first).props(
                    "outline dense")
                if state["dr_edit_id"] is not None or state["dr_rows"]:
                    ui.button("Cancel / clear form", icon="close", on_click=lambda: (clear_editor(), render_page_body())
                              ).props("outline dense")


def render_schedule_mode():
    """Mode: "Practical Time Table". Phase H: exam-date/session table
    (2.1) and faculty-availability grid (2.2). Section 2.3 (batching)
    is Phase I; Sections 3/4 (subject filter + scheduling matrix) are
    Phase J.
    """
    inst = state["logged_in"]
    year = state["ptt_year"]
    session = state["ptt_session"]

    # Saved (previously generated) time tables: look them up once per institute/year/session, and restore the
    # Level 1 / Level 2 filter they were generated with so the table is visible straight away on revisit.
    _saved_key = (inst["institute_name"], year, session)
    if state["sch4_saved_loaded_key"] != _saved_key:
        state["sch4_saved_loaded_key"] = _saved_key
        state["sch4_report"] = None
        state["sch4_report_unresolved"] = []
        state["sch4_manual_rows"] = None
        state["sch4_manual_key"] = None
        _metas = {}
        for _mode in ("auto", "manual"):
            _m = mt.load_generated_timetable(inst["institute_name"], year, session, _mode, include_rows=False)
            if _m:
                _metas[_mode] = _m
        state["sch4_saved_meta"] = _metas
        _pick = _metas.get("auto") or _metas.get("manual")
        if (_pick and not state["sch4_filter_confirmed"]
                and not state["sch4_level1_filter"] and not state["sch4_level2_filter"]):
            _l1_opts, _l2_opts = mt.get_all_level1_level2(inst["institute_name"], year, session)
            _l1 = [x for x in _pick["level1"] if x in _l1_opts]
            _l2 = [x for x in _pick["level2"] if x in _l2_opts]
            if _l1 and _l2:
                state["sch4_level1_filter"], state["sch4_level2_filter"] = _l1, _l2
                state["sch4_filter_confirmed"] = True

    ui.label("Practical Time Table").classes("text-md font-semibold")

    render_semester_date_ranges(inst["institute_name"], year, session)

    if not mt.get_date_range_groups(inst["institute_name"], year, session):
        with ui.card().classes("w-full mt-3"):
            ui.label(
                "Set a date range for at least one semester above. Everything below (Subject Filter ... "
                "Practical Time Table Report) works only on semesters that have a date range."
            ).classes("text-xs text-orange-600")
        return

    # ---------------- Subject filter ----------------
    level1_options, level2_options = mt.get_all_level1_level2(inst["institute_name"], year, session)
    if not level1_options or not level2_options:
        return

    with ui.card().classes("w-full mt-3"):
        ui.label("Subject Filter").classes("text-sm font-semibold")
        ui.label(
            "Pick every Level 1 and Level 2 option you want, THEN click Continue -- nothing "
            "below is built until you do, so picking several Level 2 options doesn't jump "
            "ahead after the first one."
        ).classes("text-xs text-gray-500")
        with ui.row().classes("w-full gap-3 mt-1"):
            def on_l1_filter(e):
                # Just record the pending selection -- no re-render here, so choosing
                # several options doesn't tear down/rebuild the widget mid-pick.
                state["sch4_level1_filter"] = e.value or []
                state["sch4_filter_confirmed"] = False

            def on_l2_filter(e):
                state["sch4_level2_filter"] = e.value or []
                state["sch4_filter_confirmed"] = False

            ui.select(
                level1_options, label="Level 1", value=state["sch4_level1_filter"], multiple=True,
                on_change=on_l1_filter,
            ).classes("flex-1").props("outlined dense use-chips")
            ui.select(
                level2_options, label="Level 2", value=state["sch4_level2_filter"], multiple=True,
                on_change=on_l2_filter,
            ).classes("flex-1").props("outlined dense use-chips")

        def confirm_subject_filter():
            if not state["sch4_level1_filter"] or not state["sch4_level2_filter"]:
                ui.notify("Select at least one Level 1 and one Level 2 option first.", type="warning")
                return
            state["sch4_filter_confirmed"] = True
            render_page_body()
            restore_scroll_positions()

        with ui.row().classes("items-center gap-2 mt-2"):
            ui.button("Continue", icon="arrow_forward", on_click=confirm_subject_filter).props(
                "unelevated color=primary"
            )
            if state["sch4_filter_confirmed"]:
                ui.icon("check_circle", color="positive").classes("text-sm")
                ui.label("Filter applied.").classes("text-xs text-green-700")
            elif state["sch4_level1_filter"] or state["sch4_level2_filter"]:
                ui.label("Selections pending -- click Continue to apply.").classes("text-xs text-orange-600")

    if not state["sch4_filter_confirmed"] or not state["sch4_level1_filter"] or not state["sch4_level2_filter"]:
        return

    # ---------------- Filtered scheduling matrix ----------------
    matrix_rows = mt.get_scheduling_matrix_rows(
        inst["institute_name"], year, session, state["sch4_level1_filter"], state["sch4_level2_filter"],
    )
    ranged_semesters = set(mt.get_semester_slot_sets(inst["institute_name"], year, session))
    matrix_rows = [r for r in matrix_rows if r["semester_label"] in ranged_semesters]  # no range -> left out
    if not matrix_rows:
        with ui.card().classes("w-full mt-3"):
            ui.label(
                "No subjects match that Level 1/Level 2 filter in a semester that has a date range."
            ).classes("text-xs text-gray-500")
        return

    render_subject_overview(inst["institute_name"], year, session, matrix_rows)
    render_semester_priority_section(matrix_rows)
    render_batch_setup_and_priority_section(matrix_rows)
    render_workshop_faculty_entry_section(matrix_rows)
    render_faculty_availability_section()

    # ---------------- Assign Day & Time (Pool R + Other Categories) ----------------
    inst_name = inst["institute_name"]
    r_done = mt.r_assignments_exist(inst_name, year, session)
    other_done = mt.other_category_assignments_exist(inst_name, year, session)

    def ask_delete_assignments():
        with ui.dialog() as dialog, ui.card():
            ui.label("Delete ALL day/time assignments?").classes("text-md font-bold text-red-700")
            ui.label(
                "This clears BOTH the Pool R assignments and every Other-Categories placement "
                "(merged and standalone) for this Year/Session, since Other Categories depends "
                "entirely on R's slots. Workshop/Faculty entries and batches are kept."
            ).classes("text-sm mt-1")

            def do_delete():
                dialog.close()
                mt.clear_all_scheduling_assignments(inst_name, year, session)
                state["assign_last_unassigned"] = []
                state["assign_other_last_unassigned"] = []
                ui.notify("All assignments deleted -- you can assign again.", type="warning")
                render_page_body()
                restore_scroll_positions()

            with ui.row().classes("gap-2 mt-3 justify-end w-full"):
                ui.button("Cancel", on_click=dialog.close).props("outline")
                ui.button("Yes, Delete", color="negative", on_click=do_delete)
        dialog.open()

    async def run_with_progress(title, func, *args):
        """Runs `func(*args, progress_cb=...)` in a background thread (so the
        websocket stays alive -- no 'trying to reconnect' banner) while showing
        a real, filling progress bar driven by that function's own progress_cb
        callback. Returns func's return value."""
        progress = {"done": 0, "total": 1}
        with ui.dialog() as prog_dialog, ui.card().classes("items-center gap-2").style("min-width: 280px;"):
            ui.label(title).classes("text-sm font-semibold")
            bar = ui.linear_progress(value=0).classes("w-64")
            pct_label = ui.label("0 / 0").classes("text-xs text-gray-500")
        prog_dialog.open()

        def tick():
            bar.value = progress["done"] / progress["total"]
            pct_label.set_text(f"{progress['done']} / {progress['total']}")

        timer = ui.timer(0.15, tick)

        def cb(done, total):
            progress["done"], progress["total"] = done, max(total, 1)

        try:
            return await run.io_bound(func, *args, progress_cb=cb)
        finally:
            timer.deactivate()
            prog_dialog.close()

    def status_row(done, done_text, pending_text):
        with ui.row().classes("items-center gap-2 mt-1"):
            ui.icon("check_circle" if done else "radio_button_unchecked",
                    color="positive" if done else "grey").classes("text-sm")
            ui.label(done_text if done else pending_text).classes(
                "text-xs " + ("text-green-700" if done else "text-gray-500"))

    with ui.card().classes("w-full mt-3"):
        ui.label("Assign Day & Time (Pool R)").classes("text-sm font-semibold")
        ui.label(
            "Every subject-batch shown above must have BOTH Workshop and Faculty saved before "
            "this can run -- rows missing either are skipped and reported as unassigned. "
            "A student is never placed in two exams in the same date+session."
        ).classes("text-xs text-gray-500")
        status_row(r_done, "Already assigned. Delete to assign again.", "Not assigned yet.")

        async def run_assign_day_time():
            result = await run_with_progress(
                "Assigning Day & Time (Pool R)...", mt.assign_day_time_pool_r, inst_name, year, session, matrix_rows,
            )
            if result.get("error"):
                ui.notify(result["error"], type="warning")
                state["assign_last_unassigned"] = []
            elif result["unassigned"]:
                ui.notify(
                    f"Assigned {result['assigned_count']} subject-batch row(s); "
                    f"{len(result['unassigned'])} could not be placed -- see the list below.",
                    type="warning",
                )
                state["assign_last_unassigned"] = result["unassigned"]
            else:
                ui.notify(f"Assigned {result['assigned_count']} subject-batch row(s).", type="positive")
                state["assign_last_unassigned"] = []
            render_page_body()
            restore_scroll_positions()

        with ui.row().classes("gap-2 mt-2"):
            ui.button("Assign Day & Time", icon="event_available", on_click=run_assign_day_time).props(
                "unelevated color=primary"
            ).set_enabled(not r_done)
            ui.button("Delete Assignments (R + Other)", icon="delete", on_click=ask_delete_assignments).props(
                "outline color=negative"
            ).set_enabled(r_done or other_done)

        if state["assign_last_unassigned"]:
            with ui.column().classes("gap-0 mt-2"):
                ui.label(f"{len(state['assign_last_unassigned'])} batch(es) could not be placed:").classes(
                    "text-xs font-semibold text-orange-600"
                )
                for u in state["assign_last_unassigned"]:
                    pc, sem, scheme, subj, l1, l2 = u["subject_key"]
                    ui.label(
                        f"{pc} / {sem} / {subj}-{l1}-{l2} batch {u['batch_index'] + 1}: {u['reason']}"
                    ).classes("text-xs text-orange-700")

    with ui.card().classes("w-full mt-3"):
        ui.label("Assign Day & Time (Other Categories)").classes("text-sm font-semibold")
        ui.label(
            "Run AFTER Pool R. A non-R student of a subject that R also takes is merged into "
            "one of that subject's R batches (same date/time, one combined row). A non-R student "
            "of a subject no R student takes gets a separate slot. Either way the same enrollment "
            "never sits two exams in the same date+session as any of its other exams -- the same "
            "date with a different session is allowed."
        ).classes("text-xs text-gray-500")
        status_row(other_done, "Already assigned. Delete to assign again.",
                   "Not assigned yet." if r_done else "Assign Pool R first.")

        async def run_assign_other_categories():
            result = await run_with_progress(
                "Assigning Day & Time (Other Categories)...", mt.assign_other_categories,
                inst_name, year, session, matrix_rows,
            )
            if result.get("error"):
                ui.notify(result["error"], type="warning")
                state["assign_other_last_unassigned"] = []
            elif result["unassigned"]:
                ui.notify(
                    f"Assigned {result['assigned_count']} placement(s); "
                    f"{len(result['unassigned'])} could not be placed -- see the list below.",
                    type="warning",
                )
                state["assign_other_last_unassigned"] = result["unassigned"]
            else:
                ui.notify(f"Assigned {result['assigned_count']} placement(s).", type="positive")
                state["assign_other_last_unassigned"] = []
            render_page_body()
            restore_scroll_positions()

        with ui.row().classes("gap-2 mt-2"):
            ui.button(
                "Assign Day & Time (Other Categories)", icon="event_available",
                on_click=run_assign_other_categories,
            ).props("unelevated color=primary").set_enabled(r_done and not other_done)
            ui.button("Delete Assignments (R + Other)", icon="delete", on_click=ask_delete_assignments).props(
                "outline color=negative"
            ).set_enabled(r_done or other_done)

        if state["assign_other_last_unassigned"]:
            with ui.column().classes("gap-0 mt-2"):
                ui.label(f"{len(state['assign_other_last_unassigned'])} could not be placed:").classes(
                    "text-xs font-semibold text-orange-600"
                )
                for u in state["assign_other_last_unassigned"]:
                    if "subject_key" in u:
                        pc, sem, scheme, subj, l1, l2 = u["subject_key"]
                        text = (f"{pc} / {sem} / {subj}-{l1}-{l2} [{u['category']}] "
                                f"batch {u['batch_index'] + 1}: {u['reason']}")
                    else:
                        text = (f"{u['enrollment']} -- {u['program_code']} / {u['semester_label']} / "
                                f"Scheme {u['scheme']} / {u['subject']}: {u.get('reason', 'could not be placed')}")
                    ui.label(text).classes("text-xs text-orange-700")

    # ---------------- Practical Time Table Report (Phase S) ----------------
    # A pure, non-reactive REPORT -- it does NOT recompute as the user types
    # or edits anything elsewhere. It only reads whatever's currently saved
    # (Batch Setup's ranges, Workshop/Faculty Entry's values, Assign Day &
    # Time's results) when the user explicitly clicks Generate/Refresh; the
    # snapshot then stays exactly as generated until the button is clicked
    # again. Every filtered subject's enrolled students are accounted for --
    # anyone who couldn't be placed shows up IN THE TABLE with a blank Date/
    # Day/Time and a Remarks explanation, never silently dropped; the
    # Unresolved section below the table just re-lists those same rows.
    inst_name = inst["institute_name"]

    def build_schedule_report_snapshot(progress_cb=None):
        return build_schedule_report_rows(inst_name, year, session, matrix_rows, False, progress_cb)

    with ui.card().classes("w-full mt-3"):
        ui.label("Practical Time Table Report -- mode").classes("text-sm font-semibold")

        def on_report_mode(e):
            state["sch4_report_mode"] = e.value
            render_page_body()
            restore_scroll_positions()

        ui.radio(
            {"auto": "Automatic (date/time assigned by the program)",
             "manual": "Manual date & time slot allocation (you choose every slot)"},
            value=state["sch4_report_mode"], on_change=on_report_mode,
        ).props("inline")

    if state["sch4_report_mode"] == "manual":
        render_manual_allocation_section(inst_name, year, session, matrix_rows, run_with_progress)
        return

    if state["sch4_report"] is None and state["sch4_saved_meta"].get("auto"):
        _saved = mt.load_generated_timetable(inst_name, year, session, "auto")
        if _saved:
            state["sch4_report"] = _saved["rows"]
            state["sch4_report_unresolved"] = _saved["unresolved"]

    with ui.card().classes("w-full mt-3"):
        with ui.row().classes("w-full items-center justify-between"):
            ui.label("Practical Time Table Report").classes("text-sm font-semibold")

            async def do_generate_report():
                snapshot, unresolved = await run_with_progress(
                    "Generating report...", build_schedule_report_snapshot,
                )
                state["sch4_report"] = snapshot
                state["sch4_report_unresolved"] = unresolved
                state["sch4_report_key"] = (year, session, tuple(state["sch4_level1_filter"]), tuple(state["sch4_level2_filter"]))
                state["sch4_saved_meta"]["auto"] = mt.save_generated_timetable(
                    inst_name, year, session, "auto", snapshot, unresolved,
                    state["sch4_level1_filter"], state["sch4_level2_filter"],
                )
                if unresolved:
                    ui.notify(
                        f"Report generated ({len(snapshot)} row(s)) -- {len(unresolved)} row(s) could not be "
                        f"fully placed, see Unresolved below the table.", type="warning",
                    )
                else:
                    ui.notify(f"Report generated ({len(snapshot)} row(s)) -- every filtered subject is scheduled.",
                              type="positive")
                render_page_body()
                restore_scroll_positions()

            async def generate_report():
                if state["sch4_saved_meta"].get("auto"):
                    _confirm_dialog(
                        "Replace the saved time table?",
                        "A time table generated earlier is saved. Generating again builds a new one from the "
                        "current data and REPLACES the saved one (dates and slots may change).",
                        do_generate_report, "Yes, replace",
                    )
                else:
                    await do_generate_report()

            def delete_saved_report():
                def go():
                    mt.delete_generated_timetable(inst_name, year, session, "auto")
                    state["sch4_saved_meta"].pop("auto", None)
                    state["sch4_report"] = None
                    state["sch4_report_unresolved"] = []
                    ui.notify("Saved time table deleted.", type="warning")
                    render_page_body()
                    restore_scroll_positions()

                _confirm_dialog("Delete the saved time table?",
                                "The saved Automatic time table is removed. Assignments are not touched.",
                                go, "Yes, delete")

            with ui.row().classes("gap-2"):
                ui.button("Generate / Refresh Report", icon="refresh", on_click=generate_report).props(
                    "unelevated color=primary"
                )

                def download_timetable_pdf():
                    path = mt.generate_practical_timetable_pdf(
                        state["sch4_report"], state.get("sch4_report_unresolved") or [],
                        inst_name, year, session,
                    )
                    ui.download(path, os.path.basename(path))

                ui.button(
                    "Download PDF", icon="picture_as_pdf", on_click=download_timetable_pdf,
                ).props("outline").set_enabled(state["sch4_report"] is not None)
                ui.button(
                    "Delete saved time table", icon="delete", on_click=delete_saved_report,
                ).props("outline color=negative").set_enabled(bool(state["sch4_saved_meta"].get("auto")))

        _render_saved_timetable_banner(inst_name, year, session, "auto")

        if state["sch4_report"] is None:
            ui.label(
                "Click Generate / Refresh Report to view the current Batch Setup and "
                "Workshop/Faculty data as a report. It won't update automatically after that -- "
                "click the button again any time you want it refreshed."
            ).classes("text-xs text-gray-500 mt-2")
            return

        ui.label(
            "Date/Day/Time pickers are placeholders here -- wired up in a later mode. "
            "This report reflects the data as of the last Generate/Refresh click. A blank "
            "Date/Day/Time means that row could not be placed -- see its Remarks column and "
            "the Unresolved list below the table."
        ).classes("text-xs text-gray-500")

        with ui.element("div").classes("w-full overflow-x-auto mt-2").props('id="ptt-matrix-scroll"'):
            with ui.column().classes("gap-1 min-w-max"):
                with ui.row().classes("gap-2 font-semibold text-xs border-b pb-1"):
                    ui.label("Sr.No").classes("w-10 flex-shrink-0")
                    ui.label("Date").classes("w-24 flex-shrink-0")
                    ui.label("Day").classes("w-20 flex-shrink-0")
                    ui.label("Time").classes("w-40 flex-shrink-0")
                    ui.label("Year").classes("w-20 flex-shrink-0")
                    ui.label("Session").classes("w-16 flex-shrink-0")
                    ui.label("Program/Semester/Scheme").classes("w-32 flex-shrink-0")
                    ui.label("Category").classes("w-20 flex-shrink-0")
                    ui.label("Total (pre)").classes("w-20 flex-shrink-0 text-center")
                    ui.label("Batch").classes("w-32 flex-shrink-0")
                    ui.label("Seat No. Range").classes("w-40 flex-shrink-0")
                    ui.label("Total (batch)").classes("w-24 flex-shrink-0 text-center")
                    ui.label("Subject").classes("w-24 flex-shrink-0")
                    ui.label("L1").classes("w-16 flex-shrink-0")
                    ui.label("L2").classes("w-16 flex-shrink-0")
                    ui.label("Workshop").classes("w-48 flex-shrink-0")
                    ui.label("Faculty").classes("w-48 flex-shrink-0")
                    ui.label("Remarks").classes("w-64 flex-shrink-0")

                for r in state["sch4_report"]:
                    row_bg = "bg-orange-50" if r.get("remark") else ""
                    with ui.row().classes(f"gap-2 items-center border-b py-1 text-sm {row_bg}"):
                        ui.label(str(r["sr_no"])).classes("w-10 flex-shrink-0")
                        ui.label(r["date"]).classes("w-24 flex-shrink-0")
                        ui.label(r["day"]).classes("w-20 flex-shrink-0")
                        ui.label(r["time"]).classes("w-40 flex-shrink-0")
                        ui.label(year).classes("w-20 flex-shrink-0")
                        ui.label(session).classes("w-16 flex-shrink-0")
                        ui.label(r["compact_code"]).classes("w-32 flex-shrink-0").tooltip(r["tooltip"])
                        ui.label(r["category"]).classes("w-20 flex-shrink-0 font-semibold")
                        ui.label(str(r["total_pre"])).classes("w-20 flex-shrink-0 text-center")
                        ui.label(r["batch_label"]).classes("w-32 flex-shrink-0 font-semibold")
                        ui.html(r["seat_range"]).classes("w-40 flex-shrink-0")
                        ui.label(r["batch_total"]).classes("w-24 flex-shrink-0 text-center")
                        ui.label(r["subject"]).classes("w-24 flex-shrink-0")
                        ui.label(r["level1"]).classes("w-16 flex-shrink-0")
                        ui.label(r["level2"]).classes("w-16 flex-shrink-0")
                        ui.label(r["workshop"]).classes("w-48 flex-shrink-0")
                        ui.label(r["faculty"]).classes("w-48 flex-shrink-0")
                        ui.label(r.get("remark", "")).classes("w-64 flex-shrink-0 text-orange-700 text-xs")

        unresolved = state.get("sch4_report_unresolved") or []
        with ui.card().classes("w-full mt-3 " + ("border-2 border-orange-300" if unresolved else "")):
            if unresolved:
                ui.label(f"Unresolved -- {len(unresolved)} row(s) not fully scheduled").classes(
                    "text-sm font-semibold text-orange-700"
                )
                ui.label(
                    "Every one of these is ALSO shown blank in the table above (same Remarks) -- "
                    "this is just a consolidated list to work through."
                ).classes("text-xs text-gray-500")
                with ui.column().classes("gap-0 mt-2 max-h-64 overflow-y-auto"):
                    for u in unresolved:
                        ui.label(
                            f"{u['compact_code']} / {u['subject']}-{u['level1']}-{u['level2']} "
                            f"[{u['category']}] (seats {u['seat_range']}): {u['remark']}"
                        ).classes("text-xs text-orange-700")
            else:
                ui.label("Nothing unresolved -- every filtered subject's students are fully scheduled.").classes(
                    "text-sm text-green-700"
                )


def _unit_key(*parts):
    """Stable text id for one schedulable unit (a batch, an individual, an other-category group)."""
    flat = []
    for p in parts:
        flat.extend(p if isinstance(p, (tuple, list)) else [p])
    return "|".join(str(x) for x in flat)


def build_schedule_report_rows(inst_name, year, session, matrix_rows, manual=False, progress_cb=None):
    """Rows of the Practical Time Table Report. manual=False: dates/times come from the automatic
    assignments. manual=True: Date/Day/Time are left blank and every row carries a "unit" key and
    its "members" (enrollments), so a slot can be chosen by hand."""
    snapshot = []
    unresolved = []
    row_configs_now = mt.get_schedule_row_configs(inst_name, year, session)
    exam_dates_by_date = {d["date"]: d for d in mt.get_exam_dates(inst_name, year, session)}
    equiv_set = mt.get_r_equivalent_categories(inst_name, year, session)
    other_schedule_now = mt.get_other_category_schedule(inst_name, year, session)
    pool_x_assignments_now = mt.get_pool_x_assignments(inst_name, year, session)
    fallback_assignments_now = mt.get_individual_fallback_assignments(inst_name, year, session)
    sr_no = 0

    def slot_display(assigned_date, assigned_session_index):
        if assigned_date and assigned_session_index is not None and assigned_session_index >= 0:
            date_str = mt.format_date_ddmmyyyy(assigned_date)
            d_info = exam_dates_by_date.get(assigned_date)
            if d_info and assigned_session_index < len(d_info["sessions"]):
                start_t, end_t = d_info["sessions"][assigned_session_index]
                return date_str, d_info["day"], f"{mt.format_time_12hr(start_t)} - {mt.format_time_12hr(end_t)}"
            if d_info:
                return date_str, d_info["day"], "--"
        return "--", "--", "--"

    def rng(members):
        return mt.compress_seat_number_ranges([m["seat_number"] for m in members])

    for row_idx, row in enumerate(matrix_rows):
        students = mt.get_students_for_subject(
            inst_name, year, session, row["program_code"], row["semester_label"],
            row["scheme"], row["subject"], row["level1"], row["level2"],
        )
        sem_num = mt.semester_number(row["semester_label"])
        compact_code = f'{row["program_code"]}-{sem_num if sem_num is not None else "?"}-{row["scheme"]}'
        tooltip = f'{row["program_code"]} / {row["semester_label"]} / Scheme {row["scheme"]}'
        subj_key = (row["program_code"], row["semester_label"], row["scheme"], row["subject"],
                    row["level1"], row["level2"])

        def make_row(category, date_str, day_str, time_str, batch_label, seat_html, total,
                     workshop, faculty, remark="", unit=None, members=None, batch_id=None):
            nonlocal sr_no
            sr_no += 1
            if manual:
                date_str, day_str, time_str = "--", "--", "--"
                remark = "" if (workshop and faculty) else "Save Workshop/Faculty first."
            snapshot.append({
                "sr_no": sr_no, "compact_code": compact_code, "tooltip": tooltip,
                "category": category,
                "date": date_str, "day": day_str, "time": time_str,
                "total_pre": len(students), "batch_label": batch_label,
                "seat_range": seat_html, "batch_total": str(total),
                "subject": row["subject"], "level1": row["level1"], "level2": row["level2"],
                "workshop": workshop or "--", "faculty": faculty or "--", "remark": remark,
                "unit": unit, "members": list(members or []), "batch_id": batch_id,
                "program_code": row["program_code"], "semester_label": row["semester_label"],
            })
            if remark and not manual:
                unresolved.append({
                    "compact_code": compact_code, "subject": row["subject"], "level1": row["level1"],
                    "level2": row["level2"], "category": category, "seat_range": seat_html, "remark": remark,
                })

        if mt.subject_has_r_students(
            inst_name, year, session, row["program_code"], row["semester_label"],
            row["scheme"], row["subject"], row["level1"], row["level2"],
        ):
            # Subject belongs to R: one row per R batch. Any other-category
            # students merged into that batch share its date/time and are
            # folded into the SAME row (category "R+X", their range in bold).
            r_ranges = mt.get_seat_number_batches(
                inst_name, year, session, row["program_code"], row["semester_label"],
                row["scheme"], category=mt.BATCH_BASE_CATEGORY,
            )
            any_r_assigned = False
            for batch_idx, (start_seat, end_seat) in enumerate(r_ranges):
                merged = mt.get_merged_batch_categories(
                    inst_name, year, session, row["program_code"], row["semester_label"],
                    row["scheme"], row["subject"], row["level1"], row["level2"],
                    batch_idx, start_seat, end_seat,
                )
                own_cfg = row_configs_now.get(subj_key + (mt.BATCH_BASE_CATEGORY, batch_idx), {})
                workshop, faculty = own_cfg.get("workshop_name", ""), own_cfg.get("faculty_name", "")
                if not (workshop and faculty):
                    workshop, faculty = mt.get_subject_workshop_faculty(row_configs_now, row["subject"])
                date_str, day_str, time_str = slot_display(
                    own_cfg.get("assigned_date", ""), own_cfg.get("assigned_session_index", -1),
                )
                if date_str != "--":
                    any_r_assigned = True
                if not merged:
                    continue
                batch_label = f"B{batch_idx + 1}"
                r_unit = _unit_key("R", subj_key, batch_idx)
                r_batch = _unit_key("RB", subj_key[0], subj_key[1], subj_key[2], batch_idx)  # the R batch itself
                r_members = [m["enrollment"] for cat in merged for m in merged[cat]]
                remark = ""
                if date_str == "--":
                    remark = ("Workshop/Faculty not saved for this batch." if not (workshop and faculty)
                              else "R not yet assigned a date/time -- run Assign Day & Time (Pool R).")
                r_keys = [c for c in merged if c == mt.BATCH_BASE_CATEGORY or c in equiv_set]
                other_keys = [c for c in merged if c not in r_keys]
                if not other_keys:
                    for c in r_keys:  # equivalents keep their real name (e.g. OTO)
                        make_row(c, date_str, day_str, time_str, batch_label,
                                 rng(merged[c]) or "--", len(merged[c]), workshop, faculty, remark,
                                 unit=r_unit, members=r_members, batch_id=r_batch)
                else:
                    parts = [rng(merged[c]) for c in r_keys if rng(merged[c])]
                    parts += [f"<b>{rng(merged[c])}</b>" for c in other_keys if rng(merged[c])]
                    make_row("+".join(r_keys + other_keys), date_str, day_str, time_str, batch_label,
                             ", ".join(parts) or "--", sum(len(merged[c]) for c in merged),
                             workshop, faculty, remark, unit=r_unit, members=r_members, batch_id=r_batch)

            # Any other-category student enrolled in this subject who was
            # NEVER merged into a batch above (pool_x_assignments has no
            # entry for them) would otherwise vanish. Two cases:
            #   - they got their OWN fresh slot instead (individual
            #     fallback -- see assign_pool_x()'s Part 1b) -> show
            #     them with that real date/time, one row per student
            #     (each may land on a different slot).
            #   - nothing worked at all -> blank-slot row per real
            #     category, same as before, so they're still visible
            #     and explained rather than silently vanishing.
            _pool_r, pool_x = mt.get_seat_number_pools(
                inst_name, year, session, row["program_code"], row["semester_label"], row["scheme"],
            )
            enrolled_set = {s["enrollment"] for s in students}
            assignments_for_subject = pool_x_assignments_now.get(subj_key, {})
            fallback_for_subject = fallback_assignments_now.get(subj_key, {})
            leftover = [
                p for p in pool_x
                if p["enrollment"] in enrolled_set and p["enrollment"] not in assignments_for_subject
            ]
            still_unplaced_by_category = {}
            for p in leftover:
                category = p.get("status") or "?"
                fb = fallback_for_subject.get(p["enrollment"])
                if fb:
                    workshop, faculty = mt.get_subject_workshop_faculty(row_configs_now, row["subject"])
                    fb_date, fb_sidx = fb
                    d_str, day_str, t_str = slot_display(fb_date, fb_sidx)
                    make_row(category, d_str, day_str, t_str, "Individual", rng([p]) or "--", 1,
                             workshop, faculty, "", unit=_unit_key("IND", subj_key, p["enrollment"]),
                             members=[p["enrollment"]])
                else:
                    still_unplaced_by_category.setdefault(category, []).append(p)
            for category in sorted(still_unplaced_by_category, key=lambda c: (c.lower(), c)):
                members = still_unplaced_by_category[category]
                workshop, faculty = mt.get_subject_workshop_faculty(row_configs_now, row["subject"])
                remark = ("This subject's R batches have no date/time yet -- run Assign Day & Time "
                          "(Pool R) first." if not any_r_assigned else
                          "Could not be merged into any R batch, and no fresh slot of its own was "
                          "found either -- every slot clashes or has no free workshop/faculty.")
                make_row(category, "--", "--", "--", "--", rng(members) or "--", len(members),
                         workshop, faculty, remark, unit=_unit_key("XG", subj_key, category),
                         members=[m["enrollment"] for m in members])
        else:
            # Subject no R student takes: each other category has its own slot/row.
            pools = mt.get_category_pools(
                inst_name, year, session, row["program_code"], row["semester_label"], row["scheme"],
            )
            for category in sorted((c for c in pools if c != mt.BATCH_BASE_CATEGORY),
                                   key=lambda c: (c.lower(), c)):
                for bi, members in mt.get_other_category_subject_batches(
                    inst_name, year, session, row["program_code"], row["semester_label"],
                    row["scheme"], row["subject"], row["level1"], row["level2"], category,
                ):
                    key = subj_key + (category, bi)
                    own_cfg = row_configs_now.get(key, {})
                    workshop, faculty = own_cfg.get("workshop_name", ""), own_cfg.get("faculty_name", "")
                    if not (workshop and faculty):
                        workshop, faculty = mt.get_subject_workshop_faculty(row_configs_now, row["subject"])
                    other_cfg = other_schedule_now.get(key, {})
                    date_str, day_str, time_str = slot_display(
                        other_cfg.get("assigned_date", ""), other_cfg.get("assigned_session_index", -1),
                    )
                    remark = ""
                    if date_str == "--":
                        remark = ("Workshop/Faculty not saved for this subject-batch." if not (workshop and faculty)
                                  else "Not yet assigned a date/time -- run Assign Day & Time (Other Categories).")
                    make_row(category, date_str, day_str, time_str, f"B{bi + 1}",
                             rng(members) or "--", len(members), workshop, faculty, remark,
                             unit=_unit_key("OC", subj_key, category, bi),
                             members=[m["enrollment"] for m in members])

        if progress_cb:
            progress_cb(row_idx + 1, len(matrix_rows))

    return snapshot, unresolved


def _manual_unit_info(rows):
    """{unit_key: {...}} for every schedulable unit of the manual table: its workshop/faculty, the
    enrollments in it, its R batch id, and what auto-fill needs for ordering (program, semester, subject)."""
    unit_info = {}
    for r in rows:
        info = unit_info.setdefault(r["unit"], {
            "key": r["unit"], "workshop": "", "faculty": "", "members": set(), "batch": r.get("batch_id"),
            "program_code": r.get("program_code"), "semester_label": r.get("semester_label"),
            "subject": r["subject"],
            "label": f'{r["compact_code"]} / {r["subject"]}-{r["level1"]}-{r["level2"]} [{r["category"]}]',
        })
        if r["workshop"] != "--":
            info["workshop"] = r["workshop"]
        if r["faculty"] != "--":
            info["faculty"] = r["faculty"]
        info["members"].update(r["members"])
    return unit_info


def render_manual_allocation_section(inst_name, year, session, matrix_rows, run_with_progress):
    """Practical Time Table Report -- MANUAL date/time slot allocation. The table has the same rows
    as the automatic report but Date/Time start blank; each batch gets a dropdown of the slots it can
    still take (see mt.compute_manual_slot_options). Saved separately from the automatic result."""
    key = (year, session, tuple(state["sch4_level1_filter"]), tuple(state["sch4_level2_filter"]))
    if state["sch4_manual_key"] != key:
        state["sch4_manual_rows"] = None
    if state["sch4_manual_rows"] is None and state["sch4_saved_meta"].get("manual"):
        _saved = mt.load_generated_timetable(inst_name, year, session, "manual")
        if _saved:
            state["sch4_manual_rows"] = _saved["rows"]
            state["sch4_manual_slots"] = mt.get_manual_schedule(inst_name, year, session)
            state["sch4_manual_auto"] = mt.get_manual_auto_keys(inst_name, year, session)
            state["sch4_manual_auto_failures"] = []
            state["sch4_manual_key"] = key

    slots = mt.get_day_slot_queue(inst_name, year, session)
    slot_by_key = {(s["date"], s["session_index"]): s for s in slots}
    allowed_by_sem = mt.get_semester_slot_sets(inst_name, year, session)  # each semester's own date range

    def slot_label(s):
        return (f'{mt.format_date_ddmmyyyy(s["date"])}  {s["day"][:3]}  |  '
                f'{mt.format_time_12hr(s["start_time"])} - {mt.format_time_12hr(s["end_time"])}')

    def opt_key(s):
        return f'{s["date"]}|{s["session_index"]}'

    def rows_with_slots():
        out = []
        for r in state["sch4_manual_rows"]:
            nr = dict(r)
            sel = state["sch4_manual_slots"].get(r["unit"])
            s = slot_by_key.get(sel) if sel else None
            if s:
                nr["date"], nr["day"] = mt.format_date_ddmmyyyy(s["date"]), s["day"]
                nr["time"] = f'{mt.format_time_12hr(s["start_time"])} - {mt.format_time_12hr(s["end_time"])}'
            else:
                nr["date"] = nr["day"] = nr["time"] = "--"
                nr["remark"] = r.get("remark") or "Date/time slot not chosen yet."
            out.append(nr)
        return out

    with ui.card().classes("w-full mt-3"):
        with ui.row().classes("w-full items-center justify-between"):
            ui.label("Practical Time Table Report -- Manual Allocation").classes("text-sm font-semibold")

            async def do_generate_manual():
                rows, _ = await run_with_progress(
                    "Building manual allocation table...", build_schedule_report_rows,
                    inst_name, year, session, matrix_rows, True,
                )
                state["sch4_manual_rows"] = rows
                state["sch4_manual_slots"] = mt.get_manual_schedule(inst_name, year, session)
                state["sch4_manual_auto"] = mt.get_manual_auto_keys(inst_name, year, session)
                state["sch4_manual_auto_failures"] = []
                state["sch4_manual_key"] = key
                state["sch4_saved_meta"]["manual"] = mt.save_generated_timetable(
                    inst_name, year, session, "manual", rows, [],
                    state["sch4_level1_filter"], state["sch4_level2_filter"],
                )
                ui.notify(f"Manual table ready ({len(rows)} row(s)).", type="positive")
                render_page_body()
                restore_scroll_positions()

            def ask_clear_all():
                with ui.dialog() as dialog, ui.card():
                    ui.label("Clear ALL manual date/time choices?").classes("text-md font-bold text-red-700")
                    ui.label("Every row goes back to blank. The automatic assignment is not touched.").classes(
                        "text-sm mt-1"
                    )

                    def do_clear():
                        dialog.close()
                        mt.clear_all_manual_schedule(inst_name, year, session)
                        state["sch4_manual_slots"] = {}
                        state["sch4_manual_auto"] = set()
                        state["sch4_manual_auto_failures"] = []
                        ui.notify("Manual allocation cleared.", type="warning")
                        render_page_body()
                        restore_scroll_positions()

                    with ui.row().classes("gap-2 mt-3 justify-end w-full"):
                        ui.button("Cancel", on_click=dialog.close).props("outline")
                        ui.button("Yes, clear", color="negative", on_click=do_clear)
                dialog.open()

            def download_manual_pdf():
                out_rows = rows_with_slots()
                unresolved = [
                    {"compact_code": r["compact_code"], "subject": r["subject"], "level1": r["level1"],
                     "level2": r["level2"], "category": r["category"], "seat_range": r["seat_range"],
                     "remark": r["remark"]}
                    for r in out_rows if r.get("remark")
                ]
                path = mt.generate_practical_timetable_pdf(
                    out_rows, unresolved, inst_name, year, session,
                    out_path=os.path.join(mt.get_institute_timetable_reports_dir(inst_name, year, session),
                                          "Practical_Time_Table_Manual.pdf"),
                    title_suffix=" (Manual Allocation)",
                )
                ui.download(path, os.path.basename(path))

            async def generate_manual():
                if state["sch4_saved_meta"].get("manual"):
                    _confirm_dialog(
                        "Replace the saved time table?",
                        "A manual time table generated earlier is saved. Generating again rebuilds the table "
                        "from the current data and REPLACES the saved one. Your chosen and auto-filled slots "
                        "are kept.",
                        do_generate_manual, "Yes, replace",
                    )
                else:
                    await do_generate_manual()

            def delete_saved_manual_table():
                def go():
                    mt.delete_generated_timetable(inst_name, year, session, "manual")
                    state["sch4_saved_meta"].pop("manual", None)
                    state["sch4_manual_rows"] = None
                    state["sch4_manual_key"] = None
                    ui.notify("Saved manual time table deleted (your slot choices are kept).", type="warning")
                    render_page_body()
                    restore_scroll_positions()

                _confirm_dialog("Delete the saved time table?",
                                "The saved Manual table is removed. The slots you chose and the auto-filled "
                                "ones are NOT deleted.", go, "Yes, delete")

            async def autofill_remaining():
                if state["sch4_manual_rows"] is None:
                    ui.notify("Generate / Refresh the manual table first.", type="warning")
                    return
                if not slots:
                    ui.notify("No exam days/sessions are set up yet.", type="warning")
                    return
                unit_info_now = _manual_unit_info(state["sch4_manual_rows"])
                units = [dict(v, members=sorted(v["members"])) for v in unit_info_now.values()]
                sem_pr = mt.get_semester_priority(
                    inst_name, year, session, sorted({u["semester_label"] for u in units}))
                subj_pr = mt.get_subject_priority(inst_name, year, session)
                availability_now = mt.get_faculty_availability(inst_name, year, session)
                new, fails = await run_with_progress(
                    "Auto-filling remaining slots...", mt.autofill_manual_slots,
                    units, slots, availability_now, dict(state["sch4_manual_slots"]), sem_pr, subj_pr,
                    allowed_by_sem,
                )
                mt.save_manual_slots_bulk(inst_name, year, session, new, is_auto=True)
                state["sch4_manual_slots"].update(new)
                state["sch4_manual_auto"] |= set(new)
                state["sch4_manual_auto_failures"] = [
                    f"{unit_info_now[k]['label']}: {reason}" for k, reason in fails.items() if k in unit_info_now
                ]
                if fails:
                    ui.notify(f"Auto-filled {len(new)} batch(es); {len(fails)} could not be placed -- see below the table.",
                              type="warning")
                else:
                    ui.notify(f"Auto-filled {len(new)} batch(es).", type="positive")
                render_page_body()
                restore_scroll_positions()

            def clear_auto_filled():
                removed = mt.clear_auto_manual_slots(inst_name, year, session)
                for k in removed:
                    state["sch4_manual_slots"].pop(k, None)
                state["sch4_manual_auto"] = set()
                state["sch4_manual_auto_failures"] = []
                ui.notify(
                    f"Cleared {len(removed)} auto-filled slot(s). Your own choices were kept." if removed
                    else "No auto-filled slots to clear.", type="positive" if removed else "info",
                )
                render_page_body()
                restore_scroll_positions()

            with ui.row().classes("gap-2"):
                ui.button("Generate / Refresh Manual Table", icon="refresh", on_click=generate_manual).props(
                    "unelevated color=primary"
                )
                ui.button("Auto-fill remaining slots", icon="auto_fix_high", on_click=autofill_remaining).props(
                    "unelevated color=secondary"
                ).set_enabled(state["sch4_manual_rows"] is not None)
                ui.button("Clear auto-filled slots", icon="layers_clear", on_click=clear_auto_filled).props(
                    "outline"
                ).set_enabled(state["sch4_manual_rows"] is not None)
                ui.button("Clear all manual allocation", icon="delete", on_click=ask_clear_all).props(
                    "outline color=negative"
                )
                ui.button("Delete saved time table", icon="delete_outline", on_click=delete_saved_manual_table).props(
                    "outline"
                ).set_enabled(bool(state["sch4_saved_meta"].get("manual")))
                ui.button("Download PDF", icon="picture_as_pdf", on_click=download_manual_pdf).props(
                    "outline"
                ).set_enabled(state["sch4_manual_rows"] is not None)

        _render_saved_timetable_banner(inst_name, year, session, "manual")

        if state["sch4_manual_rows"] is None:
            ui.label(
                "Click Generate / Refresh Manual Table to list every batch with Date/Time left blank. You "
                "then choose each slot from its dropdown -- slots where the faculty is not available, the "
                "workshop or faculty is already used, or a student already has another exam are hidden. "
                "Choices are saved automatically and are independent of the automatic assignment. "
                "After choosing the slots you care about, \"Auto-fill remaining slots\" places every other batch "
                "(your own choices are never moved), and \"Clear auto-filled slots\" removes only those."
            ).classes("text-xs text-gray-500 mt-2")
            return
        if not slots:
            ui.label("No exam days/sessions are set up yet -- add them in Exam Dates above first.").classes(
                "text-xs text-orange-600 mt-2"
            )
            return

        rows = state["sch4_manual_rows"]
        availability = mt.get_faculty_availability(inst_name, year, session)
        unit_info = _manual_unit_info(rows)

        container = ui.column().classes("w-full")

        def render_table():
            container.clear()
            assigned = state["sch4_manual_slots"]
            units = [dict(v, members=sorted(v["members"])) for v in unit_info.values()]
            options = mt.compute_manual_slot_options(units, slots, availability, assigned, allowed_by_sem)
            n_done = sum(1 for k in unit_info if assigned.get(k) in slot_by_key)

            def on_pick(e, unit_key):
                val = e.value
                if val:
                    d, si = val.split("|")
                    mt.save_manual_slot(inst_name, year, session, unit_key, d, int(si))  # is_auto=False: now the user's
                    state["sch4_manual_slots"][unit_key] = (d, int(si))
                else:
                    mt.clear_manual_slot(inst_name, year, session, unit_key)
                    state["sch4_manual_slots"].pop(unit_key, None)
                state["sch4_manual_auto"].discard(unit_key)
                render_table()

            with container:
                n_auto = sum(1 for k in unit_info if k in state["sch4_manual_auto"] and assigned.get(k) in slot_by_key)
                ui.label(
                    f"{n_done} of {len(unit_info)} batch(es) have a date/time slot"
                    + (f" ({n_auto} auto-filled, shown in green)." if n_auto else ".")
                ).classes("text-xs text-gray-600 mt-2")
                with ui.element("div").classes("w-full overflow-x-auto mt-1"):
                    with ui.column().classes("gap-1 min-w-max"):
                        with ui.row().classes("gap-2 font-semibold text-xs border-b pb-1"):
                            ui.label("Sr.No").classes("w-10 flex-shrink-0")
                            ui.label("Date & Time Slot").classes("flex-shrink-0").style("width: 22rem")
                            ui.label("Year").classes("w-20 flex-shrink-0")
                            ui.label("Session").classes("w-16 flex-shrink-0")
                            ui.label("Program/Semester/Scheme").classes("w-32 flex-shrink-0")
                            ui.label("Category").classes("w-20 flex-shrink-0")
                            ui.label("Total (pre)").classes("w-20 flex-shrink-0 text-center")
                            ui.label("Batch").classes("w-32 flex-shrink-0")
                            ui.label("Seat No. Range").classes("w-40 flex-shrink-0")
                            ui.label("Total (batch)").classes("w-24 flex-shrink-0 text-center")
                            ui.label("Subject").classes("w-24 flex-shrink-0")
                            ui.label("L1").classes("w-16 flex-shrink-0")
                            ui.label("L2").classes("w-16 flex-shrink-0")
                            ui.label("Workshop").classes("w-48 flex-shrink-0")
                            ui.label("Faculty").classes("w-48 flex-shrink-0")
                            ui.label("Remarks").classes("w-64 flex-shrink-0")

                        seen_units = set()
                        for r in rows:
                            u = r["unit"]
                            sel = assigned.get(u)
                            sel_slot = slot_by_key.get(sel) if sel else None
                            opt = options.get(u, {"slots": [], "reason": None})
                            conflict = bool(sel_slot) and slots.index(sel_slot) not in opt["slots"]
                            is_auto_row = u in state["sch4_manual_auto"] and bool(sel_slot)
                            bg = ("bg-red-50" if conflict else ("bg-orange-50" if r.get("remark")
                                  else ("bg-green-50" if is_auto_row else "")))
                            with ui.row().classes(f"gap-2 items-center border-b py-1 text-sm {bg}"):
                                ui.label(str(r["sr_no"])).classes("w-10 flex-shrink-0")

                                first = u not in seen_units
                                seen_units.add(u)
                                if not first:
                                    ui.label(slot_label(sel_slot) if sel_slot else "(same batch -- set on the first row)").classes(
                                        "text-xs text-gray-500 flex-shrink-0"
                                    ).style("width: 22rem")
                                elif not opt["slots"] and not sel_slot:
                                    ui.label(opt["reason"] or "No free slot").classes(
                                        "text-xs text-orange-700 flex-shrink-0"
                                    ).style("width: 22rem")
                                else:
                                    choices = {opt_key(slots[i]): slot_label(slots[i]) for i in opt["slots"]}
                                    cur = opt_key(sel_slot) if sel_slot else None
                                    if cur and cur not in choices:
                                        choices[cur] = slot_label(sel_slot) + "  (CLASHES NOW)"
                                    ui.select(
                                        choices, value=cur, on_change=lambda e, uk=u: on_pick(e, uk),
                                    ).props("dense outlined clearable").classes("flex-shrink-0").style("width: 22rem")

                                ui.label(year).classes("w-20 flex-shrink-0")
                                ui.label(session).classes("w-16 flex-shrink-0")
                                ui.label(r["compact_code"]).classes("w-32 flex-shrink-0").tooltip(r["tooltip"])
                                ui.label(r["category"]).classes("w-20 flex-shrink-0 font-semibold")
                                ui.label(str(r["total_pre"])).classes("w-20 flex-shrink-0 text-center")
                                ui.label(r["batch_label"]).classes("w-32 flex-shrink-0 font-semibold")
                                ui.html(r["seat_range"]).classes("w-40 flex-shrink-0")
                                ui.label(r["batch_total"]).classes("w-24 flex-shrink-0 text-center")
                                ui.label(r["subject"]).classes("w-24 flex-shrink-0")
                                ui.label(r["level1"]).classes("w-16 flex-shrink-0")
                                ui.label(r["level2"]).classes("w-16 flex-shrink-0")
                                ui.label(r["workshop"]).classes("w-48 flex-shrink-0")
                                ui.label(r["faculty"]).classes("w-48 flex-shrink-0")
                                if is_auto_row and not r.get("remark"):
                                    ui.label("auto-filled").classes("w-64 flex-shrink-0 text-green-700 text-xs")
                                else:
                                    ui.label(r.get("remark", "")).classes("w-64 flex-shrink-0 text-orange-700 text-xs")

                fails_now = state["sch4_manual_auto_failures"]
                if fails_now:
                    with ui.column().classes("gap-0 mt-2"):
                        ui.label(f"{len(fails_now)} batch(es) could not be auto-filled:").classes(
                            "text-xs font-semibold text-orange-600"
                        )
                        for line in fails_now:
                            ui.label(line).classes("text-xs text-orange-700")

        render_table()


def render_subject_overview(inst_name, year, session, matrix_rows):
    """Overview only: for the Subject Filter result, the subjects of every Program Code / Semester / Scheme and
    how many students appear for each (parent-child mapping applied, same numbers the later steps use)."""
    counts = mt.get_subject_student_counts(inst_name, year, session, matrix_rows)
    groups = []
    for r in matrix_rows:
        g = (r["program_code"], r["semester_label"], r["scheme"])
        if not groups or groups[-1][0] != g:
            groups.append((g, []))
        groups[-1][1].append(r)

    with ui.card().classes("w-full mt-3"):
        with ui.expansion(
            f"Subject Overview -- {len(groups)} program/semester/scheme group(s), {len(matrix_rows)} subject row(s)",
            icon="list_alt", value=True,
        ).classes("w-full"):
            ui.label(
                "Subjects chosen by the filter above, with the number of students appearing for each. "
                "Only semesters that have a date range are shown."
            ).classes("text-xs text-gray-500")
            columns = [
                {"name": "subject", "label": "Subject", "field": "subject", "align": "left"},
                {"name": "level1", "label": "Level 1", "field": "level1", "align": "left"},
                {"name": "level2", "label": "Level 2", "field": "level2", "align": "left"},
                {"name": "students", "label": "Students appearing", "field": "students", "align": "center"},
            ]
            current_pc = None
            for (pc, sem, scheme), rws in groups:
                if pc != current_pc:
                    ui.label(f"Program Code: {pc}").classes("text-sm font-bold text-primary mt-3")
                    current_pc = pc
                ui.label(f"{sem.title()} -- Scheme {scheme}").classes("text-xs font-semibold text-gray-600 mt-1")
                table_rows = [
                    {"id": i, "subject": r["subject"], "level1": r["level1"], "level2": r["level2"],
                     "students": counts.get((pc, sem, scheme, r["subject"], r["level1"], r["level2"]), 0)}
                    for i, r in enumerate(rws)
                ]
                ui.table(columns=columns, rows=table_rows, row_key="id").classes("w-full").props("dense flat bordered")


def render_semester_priority_section(matrix_rows):
    """Which semester's batches get first pick of exam slots -- one number per
    semester present, 1 = highest priority, no two semesters sharing a number.
    Defaults to Final/4th/2nd then 5th/3rd/1st for an Even session (the reverse for
    Odd), and applies to every program code alike. Saved, editable, and deletable
    (reverts to the default order)."""
    inst = state["logged_in"]
    year = state["ptt_year"]
    session = state["ptt_session"]

    semesters_present = sorted({r["semester_label"] for r in matrix_rows},
                               key=lambda s: mt.SEMESTER_NAMES.index(s) if s in mt.SEMESTER_NAMES else 999)
    if not semesters_present:
        return
    current = mt.get_semester_priority(inst["institute_name"], year, session, semesters_present)
    ordered = sorted(semesters_present, key=lambda s: current[s])

    for sem in ordered:
        state["sp_draft"].setdefault(sem, str(current[sem]))

    with ui.card().classes("w-full mt-3"):
        ui.label("Semester Priority").classes("text-sm font-semibold")
        ui.label(
            "1 = filled first. Every semester needs a distinct number from 1 to the count "
            "of semesters shown. Applies to every program code."
        ).classes("text-xs text-gray-500")

        with ui.row().classes("w-full gap-4 mt-2 flex-wrap"):
            for sem in ordered:
                def on_change(e, s=sem):
                    state["sp_draft"][s] = e.value

                with ui.column().classes("gap-0"):
                    ui.label(sem.title()).classes("text-xs font-semibold")
                    ui.input(value=state["sp_draft"][sem], on_change=on_change).classes("w-24").props(
                        "dense outlined type=number"
                    )

        def save_priority():
            try:
                values = {sem: int(state["sp_draft"][sem]) for sem in semesters_present}
            except (ValueError, TypeError):
                ui.notify("Every box must be a whole number.", type="warning")
                return
            if sorted(values.values()) != list(range(1, len(semesters_present) + 1)):
                ui.notify(
                    f"Numbers must be exactly 1 to {len(semesters_present)}, each used once.",
                    type="warning",
                )
                return
            mt.save_semester_priority(inst["institute_name"], year, session, values)
            ui.notify("Semester priority saved.", type="positive")
            render_page_body()
            restore_scroll_positions()

        def reset_priority():
            mt.delete_semester_priority(inst["institute_name"], year, session)
            state["sp_draft"] = {}
            ui.notify("Reset to the default order.", type="positive")
            render_page_body()
            restore_scroll_positions()

        with ui.row().classes("gap-2 mt-2"):
            ui.button("Save", icon="save", on_click=save_priority).props("unelevated color=primary dense")
            ui.button("Reset to default", icon="restart_alt", on_click=reset_priority).props("outline dense")




def render_faculty_availability_section():
    """Faculty x (exam day -> time slot) matrix -- ticked = available. A faculty with
    NO tick at all is available in NO slot until ticked.

    Rendered as ONE plain HTML table (raw checkboxes, no per-cell NiceGUI component)
    so ticking a box is purely a browser-side click -- nothing is sent to the server
    and nothing re-renders while you work. Row/column tick-all/clear-all buttons run
    the same way, entirely in the browser. Nothing is saved until you click
    'Save to Database', which reads every ticked box in one go. Saved, editable, and
    deletable (whole matrix)."""
    inst = state["logged_in"]
    year = state["ptt_year"]
    session = state["ptt_session"]

    exam_dates = [d for d in mt.get_exam_dates(inst["institute_name"], year, session) if d["is_exam_day"]]
    slots = [(d["date"], d["day"], si, st, en) for d in exam_dates for si, (st, en) in enumerate(d["sessions"])]
    faculty = mt.get_faculty_roster(inst["institute_name"], year, session)

    key = (year, session)
    if state["fa_loaded_key"] != key:
        state["fa_selected"] = set(mt.get_faculty_availability(inst["institute_name"], year, session).keys())
        state["fa_loaded_key"] = key

    with ui.card().classes("w-full mt-3"):
        ui.label("Faculty Availability").classes("text-sm font-semibold")
        ui.label(
            "Tick every date/time slot a faculty member is available for. A faculty with no "
            "tick at all cannot be scheduled in any slot until ticked. Tick everything you "
            "need, THEN click Save to Database once -- nothing is sent to the server per tick."
        ).classes("text-xs text-gray-500")

        if not exam_dates:
            ui.label("No exam days marked yet -- set them up above first.").classes("text-xs text-gray-400 mt-2")
            return
        if not faculty:
            ui.label("No faculty saved yet -- enter them in Workshop / Faculty Entry above first.").classes(
                "text-xs text-gray-400 mt-2"
            )
            return

        table_id = "fa-availability-table"
        sel_all = f"#{table_id} input[type=checkbox]"

        # Real NiceGUI buttons calling ui.run_javascript -- this is the SAME
        # mechanism "Save to Database" below already uses to read these raw
        # checkboxes, proven to actually reach them. An onclick="" attribute
        # baked directly into the raw HTML string (what this used to do) never
        # fired reliably, so it's replaced with this instead.
        def check_all_faculty_slots():
            ui.run_javascript(f"document.querySelectorAll('{sel_all}').forEach(c => c.checked = true)")

        def clear_all_faculty_slots():
            ui.run_javascript(f"document.querySelectorAll('{sel_all}').forEach(c => c.checked = false)")

        with ui.row().classes("gap-2 mt-1 mb-1"):
            ui.button(
                "Check All (every faculty, every slot)", icon="check_circle", on_click=check_all_faculty_slots,
            ).props("dense outline color=positive")
            ui.button(
                "Clear All", icon="cancel", on_click=clear_all_faculty_slots,
            ).props("dense outline color=negative")

        html = [f'<div style="overflow-x:auto; width:100%;"><table id="{table_id}" style="border-collapse:collapse;">']
        html.append("<tr><th style='padding:2px 6px;'></th>")
        for sidx, (date, day, si, st, en) in enumerate(slots):
            sel_si = f"#{table_id} input[data-si={sidx}]"
            html.append(
                f'<th style="padding:2px 6px; font-size:11px; text-align:center;">'
                f'{_esc(date)}<br><span style="color:#888;">{_esc(day[:3])}</span>'
                f'<br><span style="color:#888;">{_esc(st)}-{_esc(en)}</span><br>'
                f'<button type="button" title="Mark every faculty available" '
                f"onclick=\"document.querySelectorAll('{sel_si}').forEach(function(c){{c.checked=true}})\">"
                f'\u2713all</button> '
                f'<button type="button" title="Clear this slot for everyone" '
                f"onclick=\"document.querySelectorAll('{sel_si}').forEach(function(c){{c.checked=false}})\">"
                f'\u2717</button>'
                f'</th>'
            )
        html.append("</tr>")

        for fi, f in enumerate(faculty):
            fac = f["faculty_name"]
            sel_fi = f"#{table_id} input[data-fi={fi}]"
            html.append("<tr>")
            html.append(
                f'<td style="padding:2px 6px; font-size:12px; white-space:nowrap;">'
                f'<b>{_esc(fac)}</b><br><span style="color:#888; font-size:10px;">{_esc(", ".join(f["programs"]))}</span>'
                f'<br><button type="button" title="Mark every slot available" '
                f"onclick=\"document.querySelectorAll('{sel_fi}').forEach(function(c){{c.checked=true}})\">"
                f'\u2713all</button> '
                f'<button type="button" title="Clear this faculty" '
                f"onclick=\"document.querySelectorAll('{sel_fi}').forEach(function(c){{c.checked=false}})\">"
                f'\u2717</button>'
                f'</td>'
            )
            for sidx, (date, _day, si, _st, _en) in enumerate(slots):
                checked = "checked" if (fac, date, si) in state["fa_selected"] else ""
                html.append(
                    f'<td style="text-align:center; padding:2px;">'
                    f'<input type="checkbox" data-fi="{fi}" data-si="{sidx}" {checked}></td>'
                )
            html.append("</tr>")
        html.append("</table></div>")
        ui.html("".join(html)).classes("w-full mt-2")

        slot_lookup = [(date, si) for (date, _day, si, _st, _en) in slots]
        faculty_lookup = [f["faculty_name"] for f in faculty]

        async def save_availability():
            result = await ui.run_javascript(f"""
                const cells = [];
                document.querySelectorAll('#{table_id} input[type=checkbox]:checked').forEach(function(c) {{
                    cells.push(c.dataset.fi + '_' + c.dataset.si);
                }});
                return cells.join(',');
            """)
            selected = set()
            if result:
                for pair in result.split(","):
                    fi_s, si_s = pair.split("_")
                    fi, sidx = int(fi_s), int(si_s)
                    date, si = slot_lookup[sidx]
                    selected.add((faculty_lookup[fi], date, si))
            mt.save_faculty_availability(inst["institute_name"], year, session, selected)
            state["fa_selected"] = selected
            ui.notify(f"Saved {len(selected)} available slot(s).", type="positive")

        def delete_availability():
            mt.delete_faculty_availability(inst["institute_name"], year, session)
            state["fa_selected"] = set()
            ui.notify("Faculty availability cleared.", type="warning")
            render_page_body()
            restore_scroll_positions()

        with ui.row().classes("gap-2 mt-3"):
            ui.button("Save to Database", icon="save", on_click=save_availability).props(
                "unelevated color=primary"
            )
            ui.button("Delete All", icon="delete", on_click=delete_availability).props(
                "outline color=negative"
            )


def render_batch_setup_and_priority_section(matrix_rows):
    """ONE flat matrix table -- one row per (Program Code, Semester, Scheme)
    combo -- combining Batch Setup and Subject Priority so both live in the
    same place instead of two separate sections:
      Program Code | Semester | Scheme | R+Equivalent | Other Categories |
      Total Students | Batches (R+Equivalent) | Seat Range (R+Equivalent) |
      Batches (Other) | Seat Range (Other) | Priority
    A combo's batch-range cells stack one Start/End row per batch (since a
    group can have several batches); the Other-category columns stack one
    sub-block per OTHER category present (there can be more than one, e.g.
    X and a distinct non-equivalent category together). Priority stacks one
    "Subject: box" row per subject in that combo -- it's inherently a per-
    subject value, not a per-combo one, stored at (program, semester,
    subject) same as before (not per scheme), so the same subject showing
    up under two scheme rows in one semester shares one underlying number.
    One Save/Delete covers everything (every batch group AND every subject
    priority) in one action.
    """
    inst = state["logged_in"]
    year = state["ptt_year"]
    session = state["ptt_session"]
    base = mt.BATCH_BASE_CATEGORY

    combos = sorted(
        {(r["program_code"], r["semester_label"], r["scheme"]) for r in matrix_rows},
        key=lambda c: (c[0], mt.semester_number(c[1]) or 999, c[2]),
    )

    key = (year, session)
    if state["batchsetup_loaded_key"] != key:
        state["batchsetup_rows"] = {}
        state["batchsetup_num_input"] = {}
        state["batchsetup_loaded_key"] = key

    combo_pools = {
        c: mt.get_category_pools(inst["institute_name"], year, session, c[0], c[1], c[2]) for c in combos
    }
    equiv_set = mt.get_r_equivalent_categories(inst["institute_name"], year, session)

    for combo in combos:
        for group in combo_pools[combo]:
            gk = combo + (group,)
            if gk not in state["batchsetup_rows"]:
                ranges = mt.get_seat_number_batches(
                    inst["institute_name"], year, session, combo[0], combo[1], combo[2], category=group,
                )
                if ranges:
                    state["batchsetup_rows"][gk] = {"num_batches": str(len(ranges)), "ranges": [[s, e] for s, e in ranges]}
                else:
                    state["batchsetup_rows"][gk] = {"num_batches": "", "ranges": []}

    subjects_by_combo = {}
    subjects_by_pcsem = {}
    for r in matrix_rows:
        subjects_by_combo.setdefault((r["program_code"], r["semester_label"], r["scheme"]), set()).add(r["subject"])
        subjects_by_pcsem.setdefault((r["program_code"], r["semester_label"]), set()).add(r["subject"])

    saved_priority_cache = {}

    def ensure_priority_draft(pc, sem, subj):
        dk = f"{pc}|{sem}|{subj}"
        if dk not in state["subjp_draft"]:
            if (pc, sem) not in saved_priority_cache:
                saved_priority_cache[(pc, sem)] = mt.get_subject_priority(inst["institute_name"], year, session)
            v = saved_priority_cache[(pc, sem)].get((pc, sem, subj))
            state["subjp_draft"][dk] = str(v) if v is not None else ""
        return dk

    def render_batch_count_cell(gk, pool):
        row_cfg = state["batchsetup_rows"][gk]

        def apply_num_batches():
            raw = state["batchsetup_num_input"].get(gk, "")
            try:
                n = max(0, min(20, int(raw or 0)))
            except (ValueError, TypeError):
                n = 0
            cfg = state["batchsetup_rows"][gk]
            cfg["num_batches"] = str(n)
            seat_ints = [int(p["seat_number"]) for p in pool]
            if n and seat_ints:
                cfg["ranges"] = [list(r) for r in mt.compute_default_seat_batches(seat_ints, n)]
            else:
                cfg["ranges"] = []
            render_page_body()
            restore_scroll_positions()

        def on_draft(e):
            state["batchsetup_num_input"][gk] = e.value

        inp = ui.input(
            value=state["batchsetup_num_input"].setdefault(gk, row_cfg["num_batches"]), on_change=on_draft,
        ).classes("w-16").props("dense outlined type=number")
        inp.on("blur", apply_num_batches)
        inp.on("keydown.enter", apply_num_batches)

    def render_batch_ranges_cell(gk):
        row_cfg = state["batchsetup_rows"][gk]
        if not row_cfg["ranges"]:
            ui.label("--").classes("text-xs text-gray-400")
            return
        with ui.column().classes("gap-1"):
            for bi, rngv in enumerate(row_cfg["ranges"]):
                def on_start(e, idx=bi):
                    try:
                        state["batchsetup_rows"][gk]["ranges"][idx][0] = int(e.value)
                    except (ValueError, TypeError):
                        pass

                def on_end(e, idx=bi):
                    try:
                        state["batchsetup_rows"][gk]["ranges"][idx][1] = int(e.value)
                    except (ValueError, TypeError):
                        pass

                with ui.row().classes("items-center gap-1 flex-nowrap"):
                    ui.label(f"B{bi + 1}").classes("text-xs w-6 flex-shrink-0")
                    ui.input(value=str(rngv[0]), on_change=on_start).classes("w-24").props("dense outlined type=number")
                    ui.input(value=str(rngv[1]), on_change=on_end).classes("w-24").props("dense outlined type=number")

    with ui.card().classes("w-full mt-3"):
        ui.label("Batch Setup & Subject Priority").classes("text-sm font-semibold")
        ui.label(
            f"One row per Program/Semester/Scheme. {base} and every category set equivalent to "
            f"it form the R+Equivalent batches -- only these are used by Assign Day & Time. Every "
            f"other category gets its own batch count/ranges. Priority (1 = filled first within "
            f"its semester) is per SUBJECT, listed inside its own cell -- leave a box blank for no "
            f"priority."
        ).classes("text-xs text-gray-500")

        # Students whose seat number is not a plain number can't be put in a seat-number batch -- say so
        # instead of silently showing fewer students (or 0).
        for combo in combos:
            skipped = mt.get_unbatchable_students(inst["institute_name"], year, session, *combo)
            if skipped:
                shown = ", ".join(f"{s['enrollment']} (seat \"{s['seat_number']}\")" for s in skipped[:4])
                ui.label(
                    f"{combo[0]} / {combo[1].title()} / Scheme {combo[2]}: {len(skipped)} student(s) have no "
                    f"numeric seat number and are NOT counted or batched: {shown}{' ...' if len(skipped) > 4 else ''}"
                ).classes("text-xs text-orange-700 mt-1")

        with ui.element("div").classes("w-full overflow-x-auto mt-2 border rounded"):
            with ui.element("table").classes("border-collapse w-full text-xs"):
                with ui.element("tr").classes("sticky top-0"):
                    for h in ("Program Code", "Semester", "Scheme", "R+Equivalent", "Other Categories",
                              "Total Students", "Batches (R+Equiv)", "Seat Range (R+Equiv)",
                              "Batches (Other)", "Seat Range (Other)", "Priority"):
                        with ui.element("th").classes(
                            "border px-1 py-1 bg-gray-100 text-left text-xs font-bold"
                        ):
                            ui.label(h)

                for combo in combos:
                    pc, sem, scheme = combo
                    pools = combo_pools[combo]
                    r_keys = [c for c in pools if c == base or c in equiv_set]
                    other_keys = sorted((c for c in pools if c not in r_keys), key=lambda c: (c.lower(), c))
                    r_group = base if base in pools else (r_keys[0] if r_keys else None)

                    with ui.element("tr"):
                        with ui.element("td").classes("border px-1 py-1 align-top"):
                            ui.label(pc).classes("text-xs")
                        with ui.element("td").classes("border px-1 py-1 align-top"):
                            ui.label(sem.title()).classes("text-xs")
                        with ui.element("td").classes("border px-1 py-1 align-top"):
                            ui.label(scheme).classes("text-xs")
                        with ui.element("td").classes("border px-1 py-1 align-top"):
                            ui.label(", ".join(r_keys) if r_keys else "--").classes("text-xs")
                        with ui.element("td").classes("border px-1 py-1 align-top"):
                            ui.label(", ".join(other_keys) if other_keys else "--").classes("text-xs")
                        with ui.element("td").classes("border px-1 py-1 align-top"):
                            # R+Equivalent and every other category shown separately, each with its own count
                            with ui.column().classes("gap-0"):
                                if r_group:
                                    ui.label(f"R+Equivalent ({len(pools[r_group])})").classes("text-xs font-semibold")
                                for g in other_keys:
                                    ui.label(f"{g} ({len(pools[g])})").classes("text-xs font-semibold")
                                if not pools:
                                    ui.label("0").classes("text-xs font-semibold")

                        with ui.element("td").classes("border px-1 py-1 align-top"):
                            if r_group:
                                render_batch_count_cell(combo + (r_group,), pools[r_group])
                            else:
                                ui.label("--").classes("text-xs text-gray-400")
                        with ui.element("td").classes("border px-1 py-1 align-top"):
                            if r_group:
                                render_batch_ranges_cell(combo + (r_group,))
                            else:
                                ui.label("--").classes("text-xs text-gray-400")

                        with ui.element("td").classes("border px-1 py-1 align-top"):
                            if other_keys:
                                with ui.column().classes("gap-2"):
                                    for g in other_keys:
                                        ui.label(g).classes("text-xs text-gray-500 font-semibold")
                                        render_batch_count_cell(combo + (g,), pools[g])
                            else:
                                ui.label("--").classes("text-xs text-gray-400")
                        with ui.element("td").classes("border px-1 py-1 align-top"):
                            if other_keys:
                                with ui.column().classes("gap-2"):
                                    for g in other_keys:
                                        render_batch_ranges_cell(combo + (g,))
                            else:
                                ui.label("--").classes("text-xs text-gray-400")

                        with ui.element("td").classes("border px-1 py-1 align-top"):
                            subs = sorted(subjects_by_combo.get(combo, []))
                            with ui.column().classes("gap-1"):
                                for subj in subs:
                                    dk = ensure_priority_draft(pc, sem, subj)

                                    def on_priority_change(e, dk=dk):
                                        state["subjp_draft"][dk] = e.value

                                    with ui.row().classes("items-center gap-1 flex-nowrap"):
                                        ui.label(subj).classes("text-xs w-16 flex-shrink-0").tooltip(subj)
                                        ui.input(
                                            value=state["subjp_draft"][dk], on_change=on_priority_change,
                                        ).classes("w-14").props("dense outlined type=number")

        # ---------------- One common Save/Delete for BOTH batches AND priorities ----------------
        def save_all():
            saved_batches = 0
            for combo in combos:
                for group, pool in combo_pools[combo].items():
                    cfg = state["batchsetup_rows"][combo + (group,)]
                    if not cfg["ranges"]:
                        continue
                    ranges = [(int(s), int(e)) for s, e in cfg["ranges"]]
                    seat_ints_now = sorted(int(p["seat_number"]) for p in pool)
                    covered, overlap = set(), False
                    for s, e in ranges:
                        for n in range(s, e + 1):
                            if n in covered:
                                overlap = True
                            covered.add(n)
                    missing = [n for n in seat_ints_now if n not in covered]
                    tag = f"{combo[0]}/{combo[1]}/Scheme {combo[2]}/{group}"
                    if overlap:
                        ui.notify(f"Warning: {tag} -- batch ranges overlap, saved anyway.", type="warning")
                    if missing:
                        ui.notify(f"Warning: {tag} -- seat number(s) {missing} not covered.", type="warning")
                    mt.save_seat_number_batches(
                        inst["institute_name"], year, session, combo[0], combo[1], combo[2], ranges, category=group,
                    )
                    saved_batches += 1

            priority_groups = sorted(subjects_by_pcsem.keys())
            saved_priority_groups = 0
            for pc, sem in priority_groups:
                subjects = sorted(subjects_by_pcsem[(pc, sem)])
                values = {}
                bad = None
                for subj in subjects:
                    raw = state["subjp_draft"].get(f"{pc}|{sem}|{subj}", "").strip()
                    if raw:
                        try:
                            values[subj] = int(raw)
                        except ValueError:
                            bad = (subj, raw)
                            break
                if bad:
                    ui.notify(f"{pc} / {sem.title()}: '{bad[1]}' for {bad[0]} is not a whole number.", type="warning")
                    return
                nums = list(values.values())
                if len(nums) != len(set(nums)):
                    ui.notify(f"{pc} / {sem.title()}: two subjects share a priority number.", type="warning")
                    return
                mt.save_subject_priority(inst["institute_name"], year, session, pc, sem, values)
                saved_priority_groups += 1

            if saved_batches or saved_priority_groups:
                ui.notify(
                    f"Saved {saved_batches} batch group(s) and subject priority for "
                    f"{saved_priority_groups} program/semester group(s).", type="positive",
                )
            else:
                ui.notify("Nothing to save yet.", type="warning")
            render_page_body()
            restore_scroll_positions()

        def delete_all():
            deleted_batches = 0
            for combo in combos:
                if mt.delete_seat_number_batch_config(inst["institute_name"], year, session, combo[0], combo[1], combo[2]):
                    deleted_batches += 1
                for group in combo_pools[combo]:
                    state["batchsetup_rows"][combo + (group,)] = {"num_batches": "", "ranges": []}
                    state["batchsetup_num_input"][combo + (group,)] = ""
            for pc, sem in subjects_by_pcsem:
                mt.delete_subject_priority(inst["institute_name"], year, session, pc, sem)
            for subj_key in list(state["subjp_draft"]):
                parts = subj_key.split("|", 2)
                if len(parts) == 3 and (parts[0], parts[1]) in subjects_by_pcsem:
                    del state["subjp_draft"][subj_key]
            ui.notify(f"Deleted batches for {deleted_batches} combination(s) and all subject priorities.", type="positive")
            render_page_body()
            restore_scroll_positions()

        with ui.row().classes("gap-2 mt-3"):
            ui.button("Save to Database", icon="save", on_click=save_all).props("unelevated color=primary")
            ui.button("Delete All", icon="delete", on_click=delete_all).props("outline color=negative")

def _random_initials(used):
    """Three random capital letters not already in `used` (added to it)."""
    for _ in range(2000):
        s = "".join(random.choices(string.ascii_uppercase, k=3))
        if s not in used:
            used.add(s)
            return s
    s = "".join(random.choices(string.ascii_uppercase, k=4))
    used.add(s)
    return s


def render_workshop_faculty_entry_section(matrix_rows):
    """Workshop / Faculty Entry -- one line per subject-batch, for EVERY category
    (not just R): Program -> Semester -> Scheme -> Category -> Batch. A semester
    with no R students at all (only X, or only some other category) still gets its
    own rows here, directly.

    ONE RULE: the same subject code always gets the same workshop and faculty,
    REGARDLESS OF CATEGORY. Once a subject has a saved workshop/faculty anywhere in
    this database (any program, semester, scheme, level, category or batch -- even
    ones hidden by the current filter) that is not saved and not edited by hand
    shows the same values as an editable DRAFT. Each row still needs its own Save
    (or Save all). Saved rows and rows you edited yourself are never overwritten.
    Different values for one subject are allowed silently.

    Auto-fill (demonstration only): fills the untouched, unsaved rows -- one workshop
    (lab1, lab2 ...) and one faculty (random initials) per subject code, all names
    different -- as drafts. Unticking removes ALL saved workshop/faculty data (every
    category)."""
    inst = state["logged_in"]
    year = state["ptt_year"]
    session = state["ptt_session"]

    entry_rows = []
    for row in matrix_rows:
        pools = mt.get_category_pools(
            inst["institute_name"], year, session, row["program_code"], row["semester_label"], row["scheme"],
        )
        # Enrollments appearing for THIS subject -- looked up once per subject row, then reused to count
        # each batch's students (same grouping as mt.get_category_batch_members).
        subject_enrollments = {
            s["enrollment"] for s in mt.get_students_for_subject(
                inst["institute_name"], year, session, row["program_code"], row["semester_label"],
                row["scheme"], row["subject"], row["level1"], row["level2"],
            )
        }
        for category in pools:
            seat_ranges = mt.get_seat_number_batches(
                inst["institute_name"], year, session, row["program_code"], row["semester_label"], row["scheme"],
                category=category,
            )
            for bi, (start, end) in enumerate(seat_ranges):
                student_count = sum(
                    1 for p in pools[category]
                    if p["enrollment"] in subject_enrollments and start <= int(p["seat_number"]) <= end
                )
                if student_count == 0:
                    continue  # nobody in this batch takes this subject -- no workshop/faculty needed
                entry_rows.append({
                    "student_count": student_count,
                    "program_code": row["program_code"], "semester_label": row["semester_label"], "scheme": row["scheme"],
                    "subject": row["subject"], "level1": row["level1"], "level2": row["level2"],
                    "category": category, "batch_index": bi,
                    "batch_label": f"B{bi + 1} ({start}-{end})",
                })

    with ui.card().classes("w-full mt-3"):
        ui.label("Workshop / Faculty Entry").classes("text-sm font-semibold")
        ui.label(
            "Fill in Workshop and Faculty for each subject's batch, in every category, then "
            "Save that row. The same subject code shares one workshop and faculty across every "
            "category: once one row is saved, the subject's other rows show it as an editable "
            "draft. In the dropdowns, pick a name already used, or type a new one and press "
            "Enter to add it -- every name you save appears in the following dropdowns."
        ).classes("text-xs text-gray-500")

        if not entry_rows:
            ui.label(
                "No batch with students to show -- create batches in Batch Setup above first "
                "(batches in which no student takes the subject are hidden)."
            ).classes("text-xs text-gray-400 mt-2")
            return

        row_configs = mt.get_schedule_row_configs(inst["institute_name"], year, session)
        workshop_suggestions = mt.get_workshop_suggestions(inst["institute_name"], year, session)
        faculty_suggestions = mt.get_faculty_suggestions(inst["institute_name"], year, session)

        # Subject-level values already SAVED anywhere in this database (any program/
        # semester/scheme/category/batch).
        saved_default = {}
        for rid in sorted(row_configs):
            cfg = row_configs[rid]
            d = saved_default.setdefault(rid[3], {"workshop_name": "", "faculty_name": ""})
            if cfg["workshop_name"] and not d["workshop_name"]:
                d["workshop_name"] = cfg["workshop_name"]
            if cfg["faculty_name"] and not d["faculty_name"]:
                d["faculty_name"] = cfg["faculty_name"]

        # Demonstration auto-fill values: one workshop + one faculty per subject code.
        if state["wfentry_autofill"]:
            used_ws = {c["workshop_name"] for c in row_configs.values() if c["workshop_name"]}
            used_fac = {c["faculty_name"] for c in row_configs.values() if c["faculty_name"]}
            used_ws |= {v["workshop_name"] for v in state["wfentry_auto_values"].values()}
            used_fac |= {v["faculty_name"] for v in state["wfentry_auto_values"].values()}
            for subj in sorted({r["subject"] for r in entry_rows}):
                if subj in state["wfentry_auto_values"]:
                    continue
                d = saved_default.get(subj)
                if d and (d["workshop_name"] or d["faculty_name"]):
                    continue  # this subject already has a saved value -- copy that instead
                k = 1
                while f"lab{k}" in used_ws:
                    k += 1
                used_ws.add(f"lab{k}")
                state["wfentry_auto_values"][subj] = {
                    "workshop_name": f"lab{k}", "faculty_name": _random_initials(used_fac),
                }

        def draft_default(subj):
            d = saved_default.get(subj)
            if d and (d["workshop_name"] or d["faculty_name"]):
                return dict(d)
            if state["wfentry_autofill"] and subj in state["wfentry_auto_values"]:
                return dict(state["wfentry_auto_values"][subj])
            return {"workshop_name": "", "faculty_name": ""}

        def row_id_of(r):
            return (r["program_code"], r["semester_label"], r["scheme"],
                    r["subject"], r["level1"], r["level2"], r["category"], r["batch_index"])

        def on_autofill_toggle(e):
            was_on = state["wfentry_autofill"]
            state["wfentry_autofill"] = e.value
            if not e.value:
                state["wfentry_auto_values"] = {}
                if was_on:
                    # Testing aid: switching the demonstration auto-fill OFF removes everything saved.
                    mt.clear_all_schedule_row_configs(inst["institute_name"], year, session)
                    state["wfentry_pending"] = {}
                    state["wfentry_locked"] = {}
                    state["wfentry_touched"] = set()
                    ui.notify("Saved data is deleted.", type="warning", position="center")
            render_page_body()
            restore_scroll_positions()

        def save_all():
            saved = 0
            for r in entry_rows:
                rid = row_id_of(r)
                if state["wfentry_locked"].get(rid):
                    continue
                d = state["wfentry_pending"].get(rid)
                if not d or not (d["workshop_name"] or d["faculty_name"]):
                    continue
                mt.save_schedule_row_config(
                    inst["institute_name"], year, session, rid[0], rid[1], rid[2], rid[3], rid[4],
                    rid[5], rid[6], rid[7], d["workshop_name"], d["faculty_name"],
                )
                state["wfentry_locked"][rid] = True
                state["wfentry_touched"].discard(rid)
                saved += 1
            ui.notify(f"Saved {saved} row(s)." if saved else "Nothing to save.", type="positive" if saved else "warning")
            render_page_body()
            restore_scroll_positions()

        with ui.row().classes("items-center gap-4 mt-2"):
            ui.checkbox(
                "Auto-fill empty boxes with random values (demonstration only -- unticking deletes ALL saved workshop/faculty data)",
                value=state["wfentry_autofill"], on_change=on_autofill_toggle,
            ).props("dense")
            ui.button("Save all", icon="save", on_click=save_all).props("unelevated color=primary dense")

            def download_workshop_faculty_pdf():
                path = mt.generate_workshop_faculty_pdf(inst["institute_name"], year, session, matrix_rows)
                ui.download(path, os.path.basename(path))

            ui.button(
                "Download PDF", icon="picture_as_pdf", on_click=download_workshop_faculty_pdf,
            ).props("outline dense")

        with ui.row().classes("w-full gap-2 font-semibold text-xs border-b pb-1 mt-2"):
            ui.label("Program/Semester/Scheme").classes("w-40 flex-shrink-0")
            ui.label("Category").classes("w-16 flex-shrink-0")
            ui.label("Subject").classes("w-24 flex-shrink-0")
            ui.label("L1").classes("w-16 flex-shrink-0")
            ui.label("L2").classes("w-16 flex-shrink-0")
            ui.label("Batch").classes("w-32 flex-shrink-0")
            ui.label("No. of Students").classes("w-28 flex-shrink-0 text-center")
            ui.label("Workshop").classes("w-52 flex-shrink-0")
            ui.label("Faculty").classes("w-52 flex-shrink-0")
            ui.label("").classes("w-16 flex-shrink-0")

        for r in entry_rows:
            row_id = row_id_of(r)
            saved_cfg = row_configs.get(row_id, {})
            is_saved = bool(saved_cfg.get("workshop_name") or saved_cfg.get("faculty_name"))
            locked = state["wfentry_locked"].setdefault(row_id, is_saved)
            draft = state["wfentry_pending"].setdefault(row_id, {
                "workshop_name": saved_cfg.get("workshop_name", ""),
                "faculty_name": saved_cfg.get("faculty_name", ""),
            })
            if not locked and not is_saved and row_id not in state["wfentry_touched"]:
                draft.update(draft_default(r["subject"]))  # untouched rows follow the subject's value

            sem_num = mt.semester_number(r["semester_label"])
            compact_code = f'{r["program_code"]}-{sem_num if sem_num is not None else "?"}-{r["scheme"]}'

            with ui.row().classes("w-full gap-2 items-center border-b py-1 text-sm"):
                ui.label(compact_code).classes("w-40 flex-shrink-0").tooltip(
                    f'{r["program_code"]} / {r["semester_label"]} / Scheme {r["scheme"]}'
                )
                ui.label(r["category"]).classes("w-16 flex-shrink-0 font-semibold")
                ui.label(r["subject"]).classes("w-24 flex-shrink-0")
                ui.label(r["level1"]).classes("w-16 flex-shrink-0")
                ui.label(r["level2"]).classes("w-16 flex-shrink-0")
                ui.label(r["batch_label"]).classes("w-32 flex-shrink-0")
                ui.label(str(r["student_count"])).classes("w-28 flex-shrink-0 text-center")

                if locked:
                    ui.label(draft["workshop_name"] or "--").classes("w-52 flex-shrink-0")
                    ui.label(draft["faculty_name"] or "--").classes("w-52 flex-shrink-0")

                    def start_edit(rid=row_id):
                        state["wfentry_locked"][rid] = False
                        state["wfentry_touched"].add(rid)
                        render_page_body()
                        restore_scroll_positions()

                    ui.button("Edit", icon="edit", on_click=start_edit).props("flat dense size=sm")
                else:
                    def on_workshop_change(e, rid=row_id):
                        state["wfentry_pending"][rid]["workshop_name"] = e.value or ""
                        state["wfentry_touched"].add(rid)

                    def on_faculty_change(e, rid=row_id):
                        state["wfentry_pending"][rid]["faculty_name"] = e.value or ""
                        state["wfentry_touched"].add(rid)

                    # Dropdowns: pick a name already used, or type a new one and press Enter
                    # to add it. Every name saved so far is offered in the next dropdowns.
                    ws_options = sorted(set(workshop_suggestions) | ({draft["workshop_name"]} if draft["workshop_name"] else set()))
                    fac_options = sorted(set(faculty_suggestions) | ({draft["faculty_name"]} if draft["faculty_name"] else set()))
                    ui.select(
                        ws_options, value=draft["workshop_name"] or None, with_input=True,
                        new_value_mode="add-unique", on_change=on_workshop_change,
                    ).classes("w-52 flex-shrink-0").props("dense outlined clearable")
                    ui.select(
                        fac_options, value=draft["faculty_name"] or None, with_input=True,
                        new_value_mode="add-unique", on_change=on_faculty_change,
                    ).classes("w-52 flex-shrink-0").props("dense outlined clearable")

                    def save_row(rid=row_id):
                        d = state["wfentry_pending"][rid]
                        mt.save_schedule_row_config(
                            inst["institute_name"], year, session, rid[0], rid[1], rid[2], rid[3], rid[4],
                            rid[5], rid[6], rid[7], d["workshop_name"], d["faculty_name"],
                        )
                        state["wfentry_locked"][rid] = True
                        state["wfentry_touched"].discard(rid)
                        ui.notify("Saved.", type="positive")
                        render_page_body()
                        restore_scroll_positions()

                    ui.button("Save", icon="save", on_click=save_row).props(
                        "dense unelevated color=primary size=sm"
                    )


def render_prerequisites_mode():
    """Pre-requisites mode: Button 1 (Parent-Child Subject) only.
    Button 2 (Equivalence Subjects Between Scheme) was removed
    entirely -- the equivalence feature was tried in Practical Time
    Table's Section 4 matrix and later dropped altogether (no UI, no
    backend, no column). The database gate and Year+Session picker
    live one level up, in render_practical_timetable_screen() (Phase F)
    -- this function assumes ptt_year/ptt_session are already confirmed.
    """
    inst = state["logged_in"]
    year = state["ptt_year"]
    session = state["ptt_session"]

    program_codes = mt.get_institute_seating_chart_program_codes(inst["institute_name"], year, session)
    if not program_codes:
        with ui.card().classes("w-full"):
            ui.label("No data in this database.").classes("text-sm text-gray-500")
        return

    with ui.card().classes("w-full"):
        def open_parent_child():
            state["ptt_active_button"] = "parent_child"
            render_page_body()

        def open_category_equivalence():
            state["ptt_active_button"] = "category_equivalence"
            state["ce_loaded_key"] = None
            render_page_body()

        with ui.row().classes("gap-3"):
            ui.button(
                "Create/Edit/Delete Parent-Child Subject", icon="account_tree", on_click=open_parent_child,
            ).props("unelevated color=primary")
            ui.button(
                "Category Equivalence", icon="compare_arrows", on_click=open_category_equivalence,
            ).props("unelevated color=primary")

    if state["ptt_active_button"] == "parent_child":
        render_parent_child_screen()
    elif state["ptt_active_button"] == "category_equivalence":
        render_category_equivalence_screen()


def render_category_equivalence_screen():
    """Pre-requisites: which categories count as R. One direction only (a ticked
    category is treated as R; R is never treated as it), applied to the WHOLE
    Year+Session database. Editable and deletable at any time; changing it clears
    only the affected batches/Day-Time/Pool placements."""
    inst = state["logged_in"]
    year = state["ptt_year"]
    session = state["ptt_session"]
    base = mt.BATCH_BASE_CATEGORY

    saved = mt.get_r_equivalent_categories(inst["institute_name"], year, session)
    if state["ce_loaded_key"] != (year, session):
        state["ce_selected"] = set(saved)
        state["ce_loaded_key"] = (year, session)

    categories = mt.get_institute_categories(inst["institute_name"], year, session)
    others = [c for c in categories if c != base]

    with ui.card().classes("w-full mt-3"):
        with ui.row().classes("w-full items-center justify-between"):
            ui.label("Category Equivalence").classes("text-md font-semibold")

            def back_to_prereq():
                state["ptt_active_button"] = None
                state["ce_loaded_key"] = None
                render_page_body()

            ui.button("Back to Pre-requisites", icon="arrow_back", on_click=back_to_prereq).props("outline dense")

        ui.label(
            f"Tick every category that should be treated as {base}. Its students join the {base} "
            f"list and batches and are scheduled like {base} students. One direction only "
            f"({base} is never treated as the ticked category). Applies to all program codes, "
            f"semesters and schemes of {year} / {session}."
        ).classes("text-xs text-gray-500 mt-1")

        if base not in categories:
            ui.label(f"Note: no category named '{base}' exists in this database yet.").classes(
                "text-xs text-orange-600 mt-1"
            )
        if not others:
            ui.label(f"No categories other than '{base}' found in this database.").classes(
                "text-sm text-gray-500 mt-2"
            )
            return

        def toggle(cat, checked):
            if checked:
                state["ce_selected"].add(cat)
            else:
                state["ce_selected"].discard(cat)

        with ui.column().classes("gap-0 mt-2"):
            for c in others:
                ui.checkbox(
                    f"{c}  counts as  {base}", value=c in state["ce_selected"],
                    on_change=lambda e, cat=c: toggle(cat, e.value),
                )

        def apply_change(new_set):
            old_set = set(saved)
            mt.save_r_equivalent_categories(inst["institute_name"], year, session, sorted(new_set))
            changed = old_set ^ set(new_set)
            cleared = mt.clear_scheduling_for_categories(inst["institute_name"], year, session, sorted(changed))
            # Batch Setup screens must reload from the database.
            state["batchsetup_loaded_key"] = None
            state["batchsetup_rows"] = {}
            state["batchsetup_num_input"] = {}
            state["ce_loaded_key"] = None
            if cleared:
                ui.notify(
                    f"Saved. Batches, Day/Time and pool placements were cleared for {cleared} "
                    f"program/semester/scheme combination(s) -- redo Batch Setup for them.",
                    type="warning",
                )
            else:
                ui.notify("Category equivalence saved.", type="positive")
            render_page_body()

        with ui.row().classes("gap-2 mt-3"):
            ui.button("Save", icon="save", on_click=lambda: apply_change(set(state["ce_selected"]))).props(
                "unelevated color=primary"
            )
            ui.button("Delete all equivalences", icon="delete", on_click=lambda: apply_change(set())).props(
                "outline color=negative"
            )

        if saved:
            ui.label("Saved: " + ", ".join(f"{c} \u2192 {base}" for c in sorted(saved))).classes(
                "text-xs text-green-700 mt-2"
            )
        else:
            ui.label("Nothing saved yet -- every category is treated as itself.").classes("text-xs text-gray-500 mt-2")


def _pc_key(sem, scheme, subj, l1, l2):
    """Composite key for a subject-triple within one semester+scheme --
    used as Button 1's (parent-child) Section 2 checkbox key and as the
    row key in every section built from it. Subject/level components
    are guaranteed hyphen-free (parse_appeared_subjects rejects any
    that aren't), so joining/splitting on "|" and "-" is always safe."""
    return f"{sem}|{scheme}|{subj}|{l1}|{l2}"


def render_parent_child_screen():
    """Button 1: "Create/Edit/Delete Parent-Child Subject". Fully
    independent of Button 2; reads the globally-selected
    ptt_year/ptt_session database."""
    inst = state["logged_in"]
    year = state["ptt_year"]
    session = state["ptt_session"]

    with ui.card().classes("w-full mt-3"):
        with ui.row().classes("w-full items-center justify-between"):
            ui.label("Create/Edit/Delete Parent-Child Subject").classes("text-md font-semibold")

            def back_to_prereq():
                state["ptt_active_button"] = None
                render_page_body()

            ui.button("Back to Pre-requisites", icon="arrow_back", on_click=back_to_prereq).props(
                "outline dense"
            )

        program_codes = mt.get_institute_seating_chart_program_codes(inst["institute_name"], year, session)
        if not program_codes:
            ui.label("No data in this database.").classes("text-sm text-gray-500 mt-2")
            return

        # ---------------- Section 1 (Year read-only; Program Code + Semester editable) ----------------
        ui.label("Section 1").classes("text-sm font-semibold mt-2")
        with ui.row().classes("w-full gap-3 mt-1"):
            ui.input(label="Year", value=year).props("outlined dense readonly").classes("flex-1")

            def on_program_change(e):
                if e.value != state["pc_program_code"]:
                    state["pc_program_code"] = e.value
                    state["pc_semesters"] = []
                    state["pc_selected"] = {}
                    state["pc_child_config"] = {}
                    state["pc_edit_key"] = None
                render_page_body()

            ui.select(
                program_codes, label="Program Code", value=state["pc_program_code"], on_change=on_program_change,
            ).classes("flex-1").props("outlined dense")

            program_rows = []
            sem_options = []
            if state["pc_program_code"]:
                program_rows = mt.get_institute_seating_chart_for_program(
                    inst["institute_name"], year, session, state["pc_program_code"],
                )
                present = {r["semester_label"] for r in program_rows}
                sem_options = [s for s in mt.SEMESTER_NAMES if s in present]

            def on_semester_change(e):
                state["pc_semesters"] = e.value or []
                render_page_body()

            ui.select(
                sem_options, label="Semester", value=state["pc_semesters"], multiple=True,
                on_change=on_semester_change,
            ).classes("flex-1").props("outlined dense use-chips")

        if not state["pc_program_code"] or not state["pc_semesters"]:
            ui.label("Select a Program Code and at least one Semester to continue.").classes(
                "text-xs text-gray-500 mt-2"
            )
            return

        catalog = mt.get_subject_catalog(program_rows, semester_labels=state["pc_semesters"])
        if not catalog:
            ui.label("No subjects found for the selected semester(s).").classes("text-xs text-gray-500 mt-2")
            return

        # ---------------- Section 2: semesterwise/schemewise subject checklist ----------------
        ui.label("Section 2 -- select subjects").classes("text-sm font-semibold mt-4")
        with ui.row().classes("w-full gap-4 mt-1 flex-nowrap overflow-x-auto"):
            for sem, scheme_list in catalog:
                with ui.column().classes("min-w-64 flex-shrink-0"):
                    ui.label(sem).classes("text-sm font-semibold")
                    for scheme, triples in scheme_list:
                        ui.label(f"Scheme {scheme}").classes("text-xs font-semibold text-gray-600 mt-1")
                        for (subj, l1, l2) in triples:
                            key = _pc_key(sem, scheme, subj, l1, l2)

                            def on_check(e, k=key):
                                state["pc_selected"][k] = e.value
                                if not e.value:
                                    state["pc_child_config"].pop(k, None)
                                render_page_body()

                            ui.checkbox(
                                f"{subj}-{l1}-{l2}", value=state["pc_selected"].get(key, False), on_change=on_check,
                            ).classes("text-sm")

        # Only keys for subjects still present in the CURRENT catalog selection --
        # avoids a stale checked subject from a since-deselected semester lingering.
        selected_keys = []
        for sem, scheme_list in catalog:
            for scheme, triples in scheme_list:
                for (subj, l1, l2) in triples:
                    k = _pc_key(sem, scheme, subj, l1, l2)
                    if state["pc_selected"].get(k):
                        selected_keys.append(k)

        # ---------------- Section 3: configure Parent + Children, then save ----------------
        # (Only shown when the user has checked something new in Section 2 this
        # visit -- Section 4 below shows already-saved mappings regardless.)
        if selected_keys:
            ui.label("Section 3 -- configure parent / children").classes("text-sm font-semibold mt-4")
            for key in selected_keys:
                sem, scheme, subj, l1, l2 = key.split("|")
                cfg = state["pc_child_config"].setdefault(key, {"count": 0, "children": []})
                with ui.card().classes("w-full mt-2 bg-gray-50"):
                    ui.label(f"Parent: {subj}-{l1}-{l2}  ({sem} / {scheme})").classes("text-sm font-semibold")

                    def on_count_change(e, k=key):
                        try:
                            n = max(0, min(20, int(e.value or 0)))
                        except ValueError:
                            n = 0
                        c = state["pc_child_config"][k]
                        c["count"] = n
                        if len(c["children"]) < n:
                            c["children"] += [""] * (n - len(c["children"]))
                        else:
                            c["children"] = c["children"][:n]
                        render_page_body()

                    ui.input(
                        label="Number of children", value=str(cfg["count"]), on_change=on_count_change,
                    ).props("outlined dense type=number").classes("w-48 mt-1")

                    if cfg["count"]:
                        with ui.row().classes("w-full gap-2 mt-2 flex-wrap"):
                            for i in range(cfg["count"]):
                                def on_child_change(e, k=key, idx=i):
                                    state["pc_child_config"][k]["children"][idx] = e.value

                                ui.input(
                                    label=f"Child {i + 1} subject name",
                                    value=cfg["children"][i] if i < len(cfg["children"]) else "",
                                    on_change=on_child_change,
                                ).classes("min-w-48").props("outlined dense")

            def save_all():
                saved_any = False
                for key in selected_keys:
                    sem, scheme, subj, l1, l2 = key.split("|")
                    cfg = state["pc_child_config"].get(key, {})
                    children = [c for c in cfg.get("children", []) if c and c.strip()]
                    if not children:
                        continue
                    mt.save_parent_child_mapping(
                        inst["institute_name"], year, session, state["pc_program_code"],
                        sem, scheme, subj, l1, l2, children,
                    )
                    saved_any = True
                if saved_any:
                    ui.notify("Parent-child mapping saved.", type="positive")
                else:
                    ui.notify("Nothing to save -- add at least one child for a selected subject.", type="warning")
                render_page_body()

            ui.button("Save to Database", icon="save", on_click=save_all).classes("mt-3").props(
                "unelevated color=primary"
            )

        # ---------------- Section 4: existing mappings (edit/delete) -- shown for the
        # selected Program Code + Semester(s) regardless of Section 2/3, so already-saved
        # structure is visible immediately, not just after re-checking subjects. ----------------
        mappings = mt.get_parent_child_mappings(
            inst["institute_name"], year, session, state["pc_program_code"], state["pc_semesters"],
        )
        if mappings:
            ui.label("Section 4 -- existing parent-child mappings").classes("text-sm font-semibold mt-4")
            for m in mappings:
                mkey = _pc_key(m["semester_label"], m["scheme"], m["parent_subject"], m["parent_level1"], m["parent_level2"])
                with ui.row().classes("w-full items-center justify-between border-b py-1"):
                    ui.label(
                        f"{m['parent_subject']}-{m['parent_level1']}-{m['parent_level2']} "
                        f"({m['semester_label']} / {m['scheme']}) -> {', '.join(m['children'])}"
                    ).classes("text-sm flex-1")

                    with ui.row().classes("gap-1"):
                        def start_edit(mk=mkey, mm=m):
                            state["pc_edit_key"] = mk
                            state["pc_child_config"][mk] = {"count": len(mm["children"]), "children": list(mm["children"])}
                            render_page_body()

                        ui.button(icon="edit", on_click=start_edit).props("flat dense round size=sm")

                        def do_delete(mm=m):
                            mt.delete_parent_child_mapping(
                                inst["institute_name"], year, session, state["pc_program_code"],
                                mm["semester_label"], mm["scheme"], mm["parent_subject"],
                                mm["parent_level1"], mm["parent_level2"],
                            )
                            ui.notify("Mapping deleted.", type="positive")
                            render_page_body()

                        ui.button(icon="delete", on_click=do_delete).props(
                            "flat dense round size=sm color=negative"
                        )

                if state["pc_edit_key"] == mkey:
                    with ui.card().classes("w-full mt-1 bg-blue-50"):
                        cfg = state["pc_child_config"][mkey]

                        def on_edit_count_change(e, k=mkey):
                            try:
                                n = max(0, min(20, int(e.value or 0)))
                            except ValueError:
                                n = 0
                            c = state["pc_child_config"][k]
                            c["count"] = n
                            if len(c["children"]) < n:
                                c["children"] += [""] * (n - len(c["children"]))
                            else:
                                c["children"] = c["children"][:n]
                            render_page_body()

                        ui.input(
                            label="Number of children", value=str(cfg["count"]), on_change=on_edit_count_change,
                        ).props("outlined dense type=number").classes("w-48")

                        with ui.row().classes("w-full gap-2 mt-2 flex-wrap"):
                            for i in range(cfg["count"]):
                                def on_edit_child_change(e, k=mkey, idx=i):
                                    state["pc_child_config"][k]["children"][idx] = e.value

                                ui.input(
                                    label=f"Child {i + 1}",
                                    value=cfg["children"][i] if i < len(cfg["children"]) else "",
                                    on_change=on_edit_child_change,
                                ).classes("min-w-48").props("outlined dense")

                        def save_edit(mm=m, mk=mkey):
                            c = state["pc_child_config"][mk]
                            children = [x for x in c["children"] if x and x.strip()]
                            if not children:
                                ui.notify("Add at least one child, or use Delete instead.", type="warning")
                                return
                            mt.save_parent_child_mapping(
                                inst["institute_name"], year, session, state["pc_program_code"],
                                mm["semester_label"], mm["scheme"], mm["parent_subject"],
                                mm["parent_level1"], mm["parent_level2"], children,
                            )
                            state["pc_edit_key"] = None
                            ui.notify("Mapping updated.", type="positive")
                            render_page_body()

                        def cancel_edit():
                            state["pc_edit_key"] = None
                            render_page_body()

                        with ui.row().classes("gap-2 mt-2"):
                            ui.button("Save Changes", on_click=save_edit).props("unelevated color=primary dense")
                            ui.button("Cancel", on_click=cancel_edit).props("outline dense")


def _esc(value):
    """Escapes a value for safe interpolation into the raw HTML tables
    X Table mode builds (ui.html renders its input unescaped, so any
    pasted or manually-typed data -- student names, program codes,
    scheme letters, subject codes -- must be escaped here, or a stray
    '<', '>', or '&' in the source data could break the table markup or
    inject unintended HTML)."""
    return html_lib.escape(str(value), quote=True)


def _inst_seating_parsed_table_columns():
    """Shared column spec for every plain parsed-row table this feature
    shows (preview, saved-rows view, Add/Delete screen's main list)."""
    return [
        {"name": "enrollment", "label": "Enrollment No", "field": "enrollment", "align": "left"},
        {"name": "student_name", "label": "Student Name", "field": "student_name", "align": "left"},
        {"name": "seat_number", "label": "Seat No", "field": "seat_number", "align": "left"},
        {"name": "program_code", "label": "Program Code", "field": "program_code", "align": "left"},
        {"name": "semester_label", "label": "Semester", "field": "semester_label", "align": "left"},
        {"name": "scheme", "label": "Scheme", "field": "scheme", "align": "left"},
        {"name": "status", "label": "Regular/EX", "field": "status", "align": "left"},
        {"name": "subjects_appeared", "label": "Subjects Appeared", "field": "subjects_appeared", "align": "left"},
    ]


def render_institute_seating_chart_screen():
    """Institute-level Seating Chart -- see the module-level comment
    above the INSTITUTE-LEVEL SEATING CHART section in msbte_tool.py for
    the full "why": completely separate from Department Seating Chart,
    no shared code, no shared storage, reference/record-keeping only.

    Plan 1 flow: pick Year+Session (existing DB picker shown if any
    already exist) -> paste & Parse -> preview table (NOT yet saved) ->
    "Save to Database" (checkmark confirmation) alongside "Add/Delete
    Data" (opens a screen operating on this same parsed batch).
    """
    inst = state["logged_in"]
    with ui.row().classes("w-full items-center justify-between"):
        with ui.column().classes("gap-0"):
            ui.label("Institute Seating Chart").classes("text-xl font-bold")
            ui.label(
                "Institute-level only -- completely separate from any department's own "
                "Seating Chart. Reference/record-keeping only; nothing downstream reads it."
            ).classes("text-sm text-gray-600")

        def back_to_dashboard():
            state["institute_view"] = "dashboard"
            render_page_body()

        ui.button("Back to Dashboard", icon="arrow_back", on_click=back_to_dashboard).props("outline")

    # ---------------- Year/Session + existing-database picker ----------------
    with ui.card().classes("w-full mt-3"):
        ui.label("Year / Session").classes("text-md font-semibold")
        with ui.row().classes("w-full gap-3 mt-1"):
            def on_year(e):
                state["inst_seating_year"] = e.value

            def on_session(e):
                state["inst_seating_session"] = e.value

            ui.input(label="Year", value=state["inst_seating_year"],
                      on_change=on_year).classes("flex-1").props("outlined dense")
            ui.select(["Odd", "Even"], label="Session", value=state["inst_seating_session"],
                       on_change=on_session).classes("flex-1").props("outlined dense")

        existing_dbs = mt.list_institute_seating_chart_dbs(inst["institute_name"])
        if existing_dbs:
            ui.label("Existing databases -- click to select instead of retyping:").classes(
                "text-xs text-gray-500 mt-2"
            )
            with ui.row().classes("w-full gap-2 mt-1 flex-wrap"):
                for entry in existing_dbs:
                    def pick_existing(e=entry):
                        state["inst_seating_year"] = e["year"]
                        state["inst_seating_session"] = e["session"]
                        state["inst_seating_preview"] = None
                        state["inst_seating_preview_errors"] = []
                        render_page_body()

                    is_active = (
                        entry["year"] == state["inst_seating_year"]
                        and entry["session"] == state["inst_seating_session"]
                    )
                    ui.button(
                        f"{entry['year']} / {entry['session']}", icon="folder_open", on_click=pick_existing,
                    ).props(f"{'unelevated color=primary' if is_active else 'outline'} dense")

    # ---------------- Paste columns + Parse ----------------
    with ui.card().classes("w-full mt-3"):
        ui.label("Fill in each column from MSBTE's seating chart Excel").classes("text-md font-semibold")
        ui.label(
            "Six separate boxes, one per column -- paste (or type) that column's values, "
            "one per line, in the SAME row order in every box (line 1 of every box = "
            "row 1, line 2 = row 2, and so on)."
        ).classes("text-xs text-gray-500")
        ui.label(
            "Semester-Scheme code format: \"P-N-S\" (e.g. \"TX-4-K\") -- P is the PROGRAM "
            "CODE (kept as its own column below, since one paste here can span multiple "
            "programs at once), N is the semester number (1-6), S is the scheme letter."
        ).classes("text-xs text-gray-500")
        ui.label(
            "Subject Appeared format: comma-separated entries, each with exactly 3 "
            "hyphen-separated parts -- Subject-Level1-Level2 (e.g. \"FBT-TH-SA,FBT-PR-FA\")."
        ).classes("text-xs text-gray-500")

        ui.separator().classes("my-2")
        with ui.row().classes("w-full gap-3 mt-2 flex-nowrap overflow-x-auto"):
            for key, label in INSTITUTE_SEATING_COLUMN_SPECS:
                with ui.column().classes("flex-1 min-w-48"):
                    ui.label(label).classes("text-xs font-semibold")

                    def on_col_change(e, k=key):
                        state["inst_seating_columns"][k] = e.value

                    ui.textarea(
                        placeholder="One value per line...",
                        value=state["inst_seating_columns"][key],
                        on_change=on_col_change,
                    ).classes("w-full").props("outlined rows=8 dense")

        def parse_only():
            year = state["inst_seating_year"]
            session = state["inst_seating_session"]
            if not year.strip():
                ui.notify("Fill in Year first.", type="warning")
                return

            cols = state["inst_seating_columns"]
            split = {}
            for key, _label in INSTITUTE_SEATING_COLUMN_SPECS:
                text = (cols[key] or "").replace("\r\n", "\n").replace("\r", "\n")
                split[key] = text.split("\n") if text.strip() else []
            lengths = [len(v) for v in split.values() if v]
            if not lengths:
                ui.notify("Fill in at least the Enrollment Number column first.", type="warning")
                return
            if all((split[k][-1].strip() == "" if split[k] else True) for k, _ in INSTITUTE_SEATING_COLUMN_SPECS):
                for k in split:
                    if split[k] and split[k][-1].strip() == "":
                        split[k] = split[k][:-1]
                lengths = [len(v) for v in split.values() if v]

            n = max(lengths)
            rows = []
            for i in range(n):
                rows.append([split[key][i] if i < len(split[key]) else "" for key, _ in INSTITUTE_SEATING_COLUMN_SPECS])

            parsed, errors = mt.parse_institute_seating_chart_batch(rows)
            state["inst_seating_preview"] = parsed
            state["inst_seating_preview_errors"] = errors
            # Captured now, at parse time -- Save/Add/Delete use THESE
            # values, not the live Year/Session fields, so editing Year
            # or Session after parsing can never silently redirect a
            # save into the wrong folder.
            state["inst_seating_preview_year"] = year
            state["inst_seating_preview_session"] = session
            state["inst_seating_pending_deletes"] = []
            state["inst_seating_pending_adds"] = []
            if errors:
                ui.notify(f"Parsed {len(parsed)} row(s), {len(errors)} issue(s) -- see below.", type="warning")
            else:
                ui.notify(f"Parsed {len(parsed)} row(s).", type="positive")
            render_page_body()

        ui.button("Parse", icon="rule", on_click=parse_only).classes("mt-3").props(
            "unelevated color=primary"
        )

    # ---------------- Preview (parsed, not yet saved) ----------------
    preview = state["inst_seating_preview"]
    if preview is not None:
        with ui.card().classes("w-full mt-3"):
            ui.label(f"Preview -- {len(preview)} row(s) parsed, not yet saved").classes("text-md font-semibold")
            ui.label(
                f"Will be saved to: {state['inst_seating_preview_year']} / {state['inst_seating_preview_session']} "
                "(the Year/Session selected when Parse was clicked -- changing the fields above now won't affect this)."
            ).classes("text-xs text-gray-500")
            n_swapped = sum(1 for r in preview if r.get("swapped_columns"))
            if n_swapped:
                ui.label(
                    f"Student Name and Seat Number looked swapped in {n_swapped} row(s) -- put back the right way "
                    "round automatically."
                ).classes("text-xs text-green-700 font-semibold mt-1")
            if state["inst_seating_preview_errors"]:
                ui.label("Issues found (these rows/entries were skipped):").classes(
                    "text-xs text-red-600 font-semibold mt-1"
                )
                for err in state["inst_seating_preview_errors"][:20]:
                    ui.label(f"- {err}").classes("text-xs text-red-600")

            if preview:
                ui.table(
                    columns=_inst_seating_parsed_table_columns(), rows=preview, row_key="_key",
                ).classes("w-full mt-2")

                def save_to_database():
                    year = state["inst_seating_preview_year"]
                    session = state["inst_seating_preview_session"]
                    saved = mt.save_institute_seating_chart_rows(
                        inst["institute_name"], year, session, state["inst_seating_preview"],
                    )
                    ui.notify(f"{saved} row(s) added to database successfully.", type="positive")
                    with ui.dialog() as confirm_dialog, ui.card().classes("items-center"):
                        ui.icon("check_circle", color="positive").classes("text-5xl")
                        ui.label("Data added to database successfully").classes("text-md font-semibold mt-2")
                        ui.label(f"{saved} row(s) saved.").classes("text-sm text-gray-600")
                        ui.button("OK", on_click=confirm_dialog.close).classes("mt-3").props("unelevated color=primary")
                    confirm_dialog.open()

                def open_add_delete():
                    state["institute_view"] = "seating_chart_adddel"
                    render_page_body()

                with ui.row().classes("gap-3 mt-3"):
                    ui.button("Save to Database", icon="save", on_click=save_to_database).props(
                        "unelevated color=primary"
                    )
                    ui.button("Add/Delete Data", icon="edit_note", on_click=open_add_delete).props("outline")

    # ---------------- Already-saved rows for this Year/Session ----------------
    table = mt.get_institute_seating_chart_rows(
        inst["institute_name"], state["inst_seating_year"], state["inst_seating_session"],
    )
    if table:
        with ui.card().classes("w-full mt-3"):
            with ui.row().classes("w-full items-center justify-between"):
                ui.label(f"Saved rows for {state['inst_seating_year']} / {state['inst_seating_session']}").classes(
                    "text-md font-semibold"
                )

                def open_x_table():
                    state["institute_view"] = "x_table"
                    state["x_table_program"] = None
                    state["x_table_institute_overview"] = False
                    state["xt_filter_confirmed"] = False
                    render_page_body()

                ui.button("Open X Table", icon="grid_on", on_click=open_x_table).props("outline dense")

            ui.table(columns=_inst_seating_parsed_table_columns(), rows=table, row_key="_key").classes(
                "w-full mt-2"
            )


def render_institute_seating_adddel_screen():
    """Plan 1's Add/Delete screen -- operates ONLY on the just-parsed
    preview batch sitting in state["inst_seating_preview"], not a full
    reload of everything already in the database.

    - Each preview row gets a leading X. Clicking X moves that row out
      of the main list into a "pending deletions" table below; a single
      "Delete" button commits those deletions from the database.
    - Below that, a manual add-row form (free-text, same columns) feeds
      a "pending additions" table; a single "Add to Database" button
      commits those.
    """
    inst = state["logged_in"]
    year = state["inst_seating_preview_year"]
    session = state["inst_seating_preview_session"]

    with ui.row().classes("w-full items-center justify-between"):
        ui.label("Add / Delete Data").classes("text-xl font-bold")
        ui.label(f"{year} / {session}").classes("text-sm text-gray-600")

        def back_to_seating_chart():
            state["institute_view"] = "seating_chart"
            render_page_body()

        ui.button("Back", icon="arrow_back", on_click=back_to_seating_chart).props("outline")

    preview = state["inst_seating_preview"] or []

    # ---------------- Main parsed list with X marks ----------------
    with ui.card().classes("w-full mt-3"):
        ui.label(f"Parsed batch ({len(preview)} row(s)) -- click X to stage a row for deletion").classes(
            "text-md font-semibold"
        )
        if not preview:
            ui.label("Nothing parsed yet -- go back and Parse a batch first.").classes("text-sm text-gray-500 mt-2")
        else:
            with ui.column().classes("w-full gap-1 mt-2"):
                header_cols = [
                    "", "Enrollment No", "Student Name", "Seat No", "Program Code",
                    "Semester", "Scheme", "Regular/EX", "Subjects Appeared",
                ]
                with ui.row().classes("w-full gap-2 font-semibold text-xs border-b pb-1"):
                    for h in header_cols:
                        ui.label(h).classes("flex-1")

                def stage_delete(row):
                    preview.remove(row)
                    state["inst_seating_pending_deletes"].append(
                        (row["enrollment"], row["semester_label"], row["scheme"])
                    )
                    render_page_body()

                for row in list(preview):
                    with ui.row().classes("w-full gap-2 items-center text-sm border-b pb-1"):
                        ui.button(icon="close", on_click=lambda r=row: stage_delete(r)).props(
                            "flat dense round color=negative"
                        ).classes("flex-none")
                        ui.label(row["enrollment"]).classes("flex-1")
                        ui.label(row["student_name"]).classes("flex-1")
                        ui.label(row["seat_number"]).classes("flex-1")
                        ui.label(row["program_code"]).classes("flex-1")
                        ui.label(row["semester_label"]).classes("flex-1")
                        ui.label(row["scheme"]).classes("flex-1")
                        ui.label(row["status"]).classes("flex-1")
                        ui.label(row["subjects_appeared"]).classes("flex-1")

    # ---------------- Pending deletions ----------------
    pending_del = state["inst_seating_pending_deletes"]
    if pending_del:
        with ui.card().classes("w-full mt-3 bg-red-50"):
            ui.label(f"Pending deletions ({len(pending_del)})").classes("text-md font-semibold text-red-700")
            for enrollment, sem, scheme in pending_del:
                ui.label(f"- {enrollment} / {sem} / {scheme}").classes("text-sm text-red-700")

            def commit_deletes():
                if not year.strip():
                    ui.notify("Fill in Year first (go back to Institute Seating Chart).", type="warning")
                    return
                deleted = mt.delete_institute_seating_chart_rows(
                    inst["institute_name"], year, session, pending_del,
                )
                ui.notify(f"{deleted} row(s) deleted from database.", type="positive")
                state["inst_seating_pending_deletes"] = []
                render_page_body()

            ui.button("Delete", icon="delete", on_click=commit_deletes).classes("mt-2").props(
                "unelevated color=negative"
            )

    # ---------------- Manual add-row form ----------------
    with ui.card().classes("w-full mt-3"):
        ui.label("Add a row manually").classes("text-md font-semibold")
        with ui.row().classes("w-full gap-3 mt-2 flex-wrap"):
            for key, label in INSTITUTE_SEATING_COLUMN_SPECS:
                def on_manual_change(e, k=key):
                    state["inst_seating_manual_add"][k] = e.value

                ui.input(label=label, value=state["inst_seating_manual_add"][key],
                          on_change=on_manual_change).classes("flex-1 min-w-48").props("outlined dense")

        def stage_add():
            manual = state["inst_seating_manual_add"]
            row = [manual[key] for key, _ in INSTITUTE_SEATING_COLUMN_SPECS]
            parsed, errors = mt.parse_institute_seating_chart_batch([row])
            if errors:
                ui.notify("; ".join(errors), type="negative")
                return
            state["inst_seating_pending_adds"].append(parsed[0])
            state["inst_seating_manual_add"] = {k: "" for k, _ in INSTITUTE_SEATING_COLUMN_SPECS}
            render_page_body()

        ui.button("Add", icon="add", on_click=stage_add).classes("mt-3").props("outline")

    # ---------------- Pending additions ----------------
    pending_add = state["inst_seating_pending_adds"]
    if pending_add:
        with ui.card().classes("w-full mt-3 bg-green-50"):
            ui.label(f"Pending additions ({len(pending_add)})").classes("text-md font-semibold text-green-700")
            ui.table(columns=_inst_seating_parsed_table_columns(), rows=pending_add, row_key="_key").classes(
                "w-full mt-2"
            )

            def commit_adds():
                if not year.strip():
                    ui.notify("Fill in Year first (go back to Institute Seating Chart).", type="warning")
                    return
                added = mt.save_institute_seating_chart_rows(
                    inst["institute_name"], year, session, pending_add,
                )
                ui.notify(f"{added} row(s) added to database.", type="positive")
                state["inst_seating_pending_adds"] = []
                render_page_body()

            ui.button("Add to Database", icon="save", on_click=commit_adds).classes("mt-2").props(
                "unelevated color=primary"
            )


def render_x_table_screen():
    """X Table mode (Plan 2 shell, Phase 2): one button per unique
    Program Code found in this institute+year+session's database.
    Clicking a Program Code button opens that program's own screen
    (render_x_table_program_screen) -- fully self-contained, zero
    interrelation between different program codes.
    """
    inst = state["logged_in"]
    year = state["inst_seating_year"]
    session = state["inst_seating_session"]

    with ui.row().classes("w-full items-center justify-between"):
        with ui.column().classes("gap-0"):
            ui.label("X Table").classes("text-xl font-bold")
            ui.label(f"{year} / {session}").classes("text-sm text-gray-600")

        def back_to_seating_chart():
            state["institute_view"] = "seating_chart"
            state["x_table_program"] = None
            state["x_table_institute_overview"] = False
            render_page_body()

        ui.button("Back to Seating Chart", icon="arrow_back", on_click=back_to_seating_chart).props("outline")

    all_codes = mt.get_institute_seating_chart_program_codes(inst["institute_name"], year, session)
    if not all_codes:
        with ui.card().classes("w-full mt-3"):
            ui.label("No data saved yet for this Year/Session -- nothing to show.").classes("text-sm text-gray-500")
        return

    # Step 0: Level 1 / Level 2 filter -- everything below uses the filtered data.
    if not state["xt_filter_confirmed"] or state["xt_filter_key"] != (year, session):
        render_xt_filter_step(inst, year, session)
        return

    render_xt_filter_banner()
    l1, l2 = _xt_filters()
    program_codes = mt.get_institute_seating_chart_program_codes(inst["institute_name"], year, session, l1, l2)
    if not program_codes:
        with ui.card().classes("w-full mt-3"):
            ui.label("No students match this Level 1 / Level 2 filter.").classes("text-sm text-orange-600")
        return

    if state["x_table_institute_overview"]:
        render_x_table_institute_overview_screen(program_codes)
    elif state["x_table_program"] is None:
        with ui.card().classes("w-full mt-3"):
            ui.label("Select a Program Code").classes("text-md font-semibold")
            with ui.row().classes("w-full gap-2 mt-2 flex-wrap"):
                for code in program_codes:
                    def pick_program(c=code):
                        state["x_table_program"] = c
                        render_page_body()

                    ui.button(code, icon="school", on_click=pick_program).props("unelevated color=primary")

                def open_institute_overview():
                    state["x_table_institute_overview"] = True
                    render_page_body()

                ui.button(
                    "Institute X Table Overview", icon="public", on_click=open_institute_overview,
                ).props("outline color=primary")
    else:
        render_x_table_program_screen(program_codes)


def _xt_filters():
    """(level1_list, level2_list) of the applied X Table filter, or (None, None) if none."""
    if state["xt_filter_confirmed"] and state["xt_level1_filter"] and state["xt_level2_filter"]:
        return list(state["xt_level1_filter"]), list(state["xt_level2_filter"])
    return None, None


def _xt_filter_text():
    l1, l2 = _xt_filters()
    if l1 is None:
        return "No filter (all subjects)"
    return f"Level 1: {', '.join(l1)}  |  Level 2: {', '.join(l2)}"


def render_xt_filter_step(inst, year, session):
    """Step 0 of X Table: choose Level 1 and Level 2 (each multi-select) before anything else."""
    l1_opts, l2_opts = mt.get_all_level1_level2(inst["institute_name"], year, session)
    with ui.card().classes("w-full mt-3"):
        ui.label("Filter subjects (Level 1 / Level 2)").classes("text-md font-semibold")

        def confirm(empty=False):
            if not empty and (not state["xt_level1_filter"] or not state["xt_level2_filter"]):
                ui.notify("Select at least one Level 1 and one Level 2 option first.", type="warning")
                return
            if empty:
                state["xt_level1_filter"], state["xt_level2_filter"] = [], []
            state["xt_filter_confirmed"] = True
            state["xt_filter_key"] = (year, session)
            state["x_table_program"] = None
            state["x_table_institute_overview"] = False
            render_page_body()

        if not l1_opts or not l2_opts:
            ui.label("No subject data found in this database, so there is nothing to filter.").classes(
                "text-xs text-gray-500"
            )
            ui.button("Continue without filter", icon="arrow_forward", on_click=lambda: confirm(True)).props(
                "unelevated color=primary"
            ).classes("mt-2")
            return

        state["xt_level1_filter"] = [x for x in state["xt_level1_filter"] if x in l1_opts]
        state["xt_level2_filter"] = [x for x in state["xt_level2_filter"] if x in l2_opts]
        ui.label(
            "Choose the Level 1 and Level 2 options to include, then click Continue. A student is "
            "counted only if at least one of their subjects has a selected Level 1 AND a selected "
            "Level 2 (on the same subject entry). Every X Table view below uses this filtered data."
        ).classes("text-xs text-gray-500")

        def on_l1(e):
            state["xt_level1_filter"] = e.value or []

        def on_l2(e):
            state["xt_level2_filter"] = e.value or []

        with ui.row().classes("w-full gap-3 mt-2"):
            ui.select(l1_opts, label="Level 1", value=state["xt_level1_filter"], multiple=True,
                      on_change=on_l1).classes("flex-1").props("outlined dense use-chips")
            ui.select(l2_opts, label="Level 2", value=state["xt_level2_filter"], multiple=True,
                      on_change=on_l2).classes("flex-1").props("outlined dense use-chips")
        ui.button("Continue", icon="arrow_forward", on_click=lambda: confirm(False)).props(
            "unelevated color=primary"
        ).classes("mt-2")


def render_xt_filter_banner():
    with ui.row().classes("w-full items-center gap-3 mt-2"):
        ui.label(f"Filter -- {_xt_filter_text()}").classes("text-xs text-blue-700 font-semibold")

        def change_filter():
            state["xt_filter_confirmed"] = False
            state["x_table_program"] = None
            state["x_table_institute_overview"] = False
            render_page_body()

        ui.button("Change filter", icon="filter_alt", on_click=change_filter).props("outline dense")


_XT_CELL_CLASSES = {
    "hdrfix": "border px-2 py-1 bg-gray-100 align-bottom",
    "hdr": "border px-2 py-1 bg-blue-50 text-center",
    "hdrsub": "border px-2 py-1 bg-gray-100 text-center",
    "count": "border px-2 py-1 text-center",
    "total": "border px-2 py-1 text-center font-semibold bg-blue-50",
    "totallabel": "border px-2 py-1 font-semibold bg-blue-50",
    "progtotal": "border px-2 py-1 text-center font-bold bg-blue-100",
    "grand": "border px-2 py-1 text-center font-bold bg-blue-200",
}


def render_grid_model_html(model):
    """On-screen version of an mt.xt_*_model() grid (same model the PDF/CSV are built from)."""
    parts = ['<table class="border-collapse text-xs w-full">']
    for rows, is_header in ((model["header"], True), (model["body"], False)):
        for row in rows:
            parts.append("<tr>")
            tag = "th" if is_header else "td"
            for cell in row:
                attrs = ""
                if cell["colspan"] > 1:
                    attrs += f' colspan="{cell["colspan"]}"'
                if cell["rowspan"] > 1:
                    attrs += f' rowspan="{cell["rowspan"]}"'
                cls = _XT_CELL_CLASSES.get(cell["kind"], "border px-2 py-1")
                parts.append(f'<{tag}{attrs} class="{cls}">{_esc(cell["text"])}</{tag}>')
            parts.append("</tr>")
    parts.append("</table>")
    ui.html("".join(parts)).classes("w-full overflow-x-auto")


def render_xt_downloads(model, file_stub, extra_lines=()):
    """Download PDF / Download CSV buttons for an X Table grid model."""
    inst = state["logged_in"]
    year = state["inst_seating_year"]
    session = state["inst_seating_session"]
    safe = "".join(ch if ch.isalnum() else "_" for ch in f"{file_stub}_{year}_{session}")

    def out(ext):
        return os.path.join(mt.get_institute_timetable_reports_dir(inst["institute_name"], year, session),
                            f"{safe}.{ext}")

    def download_pdf():
        lines = [inst["institute_name"], model["title"], f"Year / Session: {year} / {session}",
                 *extra_lines, f"Filter -- {_xt_filter_text()}"]
        path = mt.xt_model_to_pdf(model, out("pdf"), lines)
        ui.download(path, os.path.basename(path))

    def download_csv():
        path = mt.xt_model_to_csv(model, out("csv"))
        ui.download(path, os.path.basename(path))

    with ui.row().classes("gap-2 mt-2"):
        ui.button("Download PDF", icon="picture_as_pdf", on_click=download_pdf).props("outline dense")
        ui.button("Download CSV", icon="table_view", on_click=download_csv).props("outline dense")


def _semester_scheme_status_header_html(groups):
    """Shared 3-row header fragment (Semester > Scheme > category) used by the count,
    overview and institute-overview tables -- built from _semester_scheme_groups()'s
    `groups` output: [(semester, [(scheme, [category, ...]), ...]), ...]. Only
    categories that have data get a column. Returns (row1, row2, row3) strings."""
    row1, row2, row3 = [], [], []
    for sem, schemes in groups:
        span = sum(len(cats) for _scheme, cats in schemes)
        row1.append(f'<th colspan="{span}" class="border px-2 py-1 bg-blue-50">{_esc(sem)}</th>')
    for sem, schemes in groups:
        for scheme, cats in schemes:
            row2.append(f'<th colspan="{len(cats)}" class="border px-2 py-1 bg-blue-50">{_esc(scheme)}</th>')
    for sem, schemes in groups:
        for _scheme, cats in schemes:
            for cat in cats:
                row3.append(f'<th class="border px-2 py-1 bg-gray-100">{_esc(cat)}</th>')
    return "".join(row1), "".join(row2), "".join(row3)


def render_semesterwise_count_table(year, session, program_code, program_rows):
    """Plan 4: Semesterwise Student Count -- counts per semester/scheme/category, a
    per-semester Total row, and a Grand Total row (all semesters); PDF and CSV download."""
    model = mt.xt_count_table_model(year, session, program_code, program_rows)
    if model is None:
        ui.label("No data for this program code.").classes("text-xs text-gray-500 mt-1")
        return
    render_grid_model_html(model)
    render_xt_downloads(model, f"X_Table_Count_{program_code}", extra_lines=(f"Program Code: {program_code}",))


def render_semesterwise_overview_table(year, session, program_code, program_rows):
    """Plan 3: Semesterwise Overview -- one row per enrollment number,
    tick marks under whichever semester -> scheme -> Regular/EX cell
    matches that student's actual record for that semester."""
    groups, flat_columns, rows = mt.build_semesterwise_overview(program_rows)
    if not groups:
        ui.label("No data for this program code.").classes("text-xs text-gray-500 mt-1")
        return

    row1, row2, row3 = _semester_scheme_status_header_html(groups)
    fixed_labels = ("Sr. No.", "Year", "Program Code", "Semester (Odd/Even)", "Enrollment No", "Student Name")

    html = ['<table class="border-collapse text-xs w-full">']
    html.append("<tr>")
    for label in fixed_labels:
        html.append(f'<th rowspan="3" class="border px-2 py-1 bg-gray-100 align-bottom">{label}</th>')
    html.append(row1)
    html.append("</tr>")
    html.append(f"<tr>{row2}</tr>")
    html.append(f"<tr>{row3}</tr>")

    for i, r in enumerate(rows, start=1):
        html.append("<tr>")
        html.append(f'<td class="border px-2 py-1">{i}</td>')
        html.append(f'<td class="border px-2 py-1">{_esc(year)}</td>')
        html.append(f'<td class="border px-2 py-1">{_esc(program_code)}</td>')
        html.append(f'<td class="border px-2 py-1">{_esc(session)}</td>')
        html.append(f'<td class="border px-2 py-1">{_esc(r["enrollment"])}</td>')
        html.append(f'<td class="border px-2 py-1">{_esc(r["student_name"])}</td>')
        for col in flat_columns:
            if r["ticks"].get(col):
                html.append('<td class="border px-2 py-1 text-center text-green-600 font-bold">&#10003;</td>')
            else:
                html.append('<td class="border px-2 py-1"></td>')
        html.append("</tr>")
    html.append("</table>")
    ui.html("".join(html)).classes("w-full overflow-x-auto")


def render_x_table_institute_overview_screen(program_codes):
    """Plan 5: "Institute X Table Overview" -- one shared matrix spanning
    all program codes, each contributing its own Regular/EX-count row
    pair under a common semester -> scheme -> Regular/EX header (union
    across all program codes, so every program lines up under the same
    columns even where it has no data for some of them)."""
    inst = state["logged_in"]
    year = state["inst_seating_year"]
    session = state["inst_seating_session"]

    with ui.row().classes("w-full items-center justify-between mt-3"):
        ui.label("Institute X Table Overview").classes("text-lg font-bold")

        def back_to_program_list():
            state["x_table_institute_overview"] = False
            render_page_body()

        ui.button("Back to Program List", icon="arrow_back", on_click=back_to_program_list).props("outline dense")

    l1, l2 = _xt_filters()
    groups, flat_columns, per_program = mt.build_institute_x_table_overview(
        inst["institute_name"], year, session, l1, l2,
    )
    model = mt.xt_institute_overview_model(year, session, groups, flat_columns, per_program)
    if model is None:
        with ui.card().classes("w-full mt-3"):
            ui.label("No data available.").classes("text-sm text-gray-500")
        return

    with ui.card().classes("w-full mt-3"):
        render_grid_model_html(model)
        render_xt_downloads(model, "Institute_X_Table_Overview")


def render_x_table_program_screen(program_codes):
    """One Program Code's X Table screen (Plan 2): collapsible sections
    per semester, each containing one SEPARATE matrix table per scheme
    (never merged across schemes). Fully self-contained to this program
    code -- built only from get_institute_seating_chart_for_program()'s
    rows for THIS code.
    """
    inst = state["logged_in"]
    year = state["inst_seating_year"]
    session = state["inst_seating_session"]
    program_code = state["x_table_program"]

    with ui.row().classes("w-full items-center justify-between mt-3"):
        ui.label(f"Program Code: {program_code}").classes("text-lg font-bold")

        def back_to_program_list():
            state["x_table_program"] = None
            render_page_body()

        with ui.row().classes("gap-2"):
            for code in program_codes:
                if code != program_code:
                    def switch_program(c=code):
                        state["x_table_program"] = c
                        render_page_body()

                    ui.button(code, on_click=switch_program).props("outline dense")
            ui.button("Back to Program List", icon="arrow_back", on_click=back_to_program_list).props("outline dense")

    l1, l2 = _xt_filters()
    program_rows = mt.get_institute_seating_chart_for_program(
        inst["institute_name"], year, session, program_code, l1, l2,
    )
    grouped = mt.group_program_rows_by_semester_scheme(program_rows)

    if not grouped:
        with ui.card().classes("w-full mt-3"):
            ui.label("No data for this program code.").classes("text-sm text-gray-500")
        return

    # ---------------- Plan 4: Semesterwise Student Count ----------------
    with ui.expansion("Semesterwise Student Count", icon="functions").classes("w-full mt-2 border"):
        render_semesterwise_count_table(year, session, program_code, program_rows)

    # ---------------- Plan 3: Semesterwise Overview ----------------
    with ui.expansion(f"Semesterwise Overview of {program_code}", icon="table_view").classes("w-full mt-2 border"):
        render_semesterwise_overview_table(year, session, program_code, program_rows)

    # ---------------- Plan 2: per-semester, per-scheme detail matrices ----------------
    for semester_label, scheme_list in grouped:
        with ui.expansion(semester_label, icon="event_note").classes("w-full mt-2 border"):
            for scheme, rows_for_scheme in scheme_list:
                with ui.card().classes("w-full mt-2"):
                    ui.label(f"Scheme: {scheme}").classes("text-sm font-semibold")
                    columns, matrix_rows = mt.build_x_table_matrix(rows_for_scheme)

                    if not columns:
                        ui.label("No Appeared Subjects data for this scheme.").classes(
                            "text-xs text-gray-500 mt-1"
                        )
                        continue

                    # The fixed/subject header (3-row rowspan/colspan structure)
                    # control over the 3-row rowspan/colspan structure that
                    # ui.table's column model can't express.
                    subject_groups = []
                    seen_subjects = []
                    for (subj, l1, l2) in columns:
                        if not seen_subjects or seen_subjects[-1] != subj:
                            seen_subjects.append(subj)
                            subject_groups.append({"subject": subj, "cols": []})
                        subject_groups[-1]["cols"].append((l1, l2))

                    fixed_labels = (
                        "Sr. No.", "Year", "Semester (Odd/Even)", "Semester", "Program Code",
                        "Scheme", "Enrollment No", "Student Name", "Category",
                    )
                    html_parts = ['<table class="border-collapse text-xs w-full">']
                    # Row 1
                    html_parts.append("<tr>")
                    for fixed_label in fixed_labels:
                        html_parts.append(
                            f'<th rowspan="3" class="border px-2 py-1 bg-gray-100 align-bottom">{fixed_label}</th>'
                        )
                    for grp in subject_groups:
                        html_parts.append(
                            f'<th colspan="{len(grp["cols"])}" class="border px-2 py-1 bg-blue-50">{_esc(grp["subject"])}</th>'
                        )
                    html_parts.append("</tr>")
                    # Row 2: Level 1 components
                    html_parts.append("<tr>")
                    for grp in subject_groups:
                        l1_groups = []
                        for (l1, l2) in grp["cols"]:
                            if not l1_groups or l1_groups[-1]["l1"] != l1:
                                l1_groups.append({"l1": l1, "count": 0})
                            l1_groups[-1]["count"] += 1
                        for lg in l1_groups:
                            html_parts.append(
                                f'<th colspan="{lg["count"]}" class="border px-2 py-1 bg-blue-50">{_esc(lg["l1"])}</th>'
                            )
                    html_parts.append("</tr>")
                    # Row 3: Level 2 components
                    html_parts.append("<tr>")
                    for grp in subject_groups:
                        for (l1, l2) in grp["cols"]:
                            html_parts.append(f'<th class="border px-2 py-1 bg-blue-50">{_esc(l2)}</th>')
                    html_parts.append("</tr>")
                    # Data rows
                    for i, r in enumerate(matrix_rows, start=1):
                        html_parts.append("<tr>")
                        html_parts.append(f'<td class="border px-2 py-1">{i}</td>')
                        html_parts.append(f'<td class="border px-2 py-1">{_esc(year)}</td>')
                        html_parts.append(f'<td class="border px-2 py-1">{_esc(session)}</td>')
                        html_parts.append(f'<td class="border px-2 py-1">{_esc(semester_label)}</td>')
                        html_parts.append(f'<td class="border px-2 py-1">{_esc(program_code)}</td>')
                        html_parts.append(f'<td class="border px-2 py-1">{_esc(scheme)}</td>')
                        html_parts.append(f'<td class="border px-2 py-1">{_esc(r["enrollment"])}</td>')
                        html_parts.append(f'<td class="border px-2 py-1">{_esc(r["student_name"])}</td>')
                        html_parts.append(f'<td class="border px-2 py-1">{_esc(r["status"])}</td>')
                        for col in columns:
                            if r["ticks"][col]:
                                html_parts.append(
                                    '<td class="border px-2 py-1 text-center text-green-600 font-bold">&#10003;</td>'
                                )
                            else:
                                html_parts.append('<td class="border px-2 py-1"></td>')
                        html_parts.append("</tr>")
                    html_parts.append("</table>")
                    ui.html("".join(html_parts)).classes("w-full overflow-x-auto")


def render_page_body():
    """The ONE place that decides what this connection sees: the auth
    flow (not logged in), the Institute Dashboard (logged in as an
    Institute), or the existing Seating Chart Group + Global Scheme
    Group UI (logged in as a Department) -- exactly as that UI worked
    before login existed, completely unchanged.
    """
    global content_container, top_container

    page_container.clear()
    with page_container:
        if state["logged_in"] is None:
            with ui.column().classes("w-full items-center"):
                view = state["auth_view"]
                if view == "signup":
                    render_signup_screen()
                elif view == "forgot":
                    render_forgot_screen()
                else:
                    render_login_screen()
            return

        if state["logged_in"]["type"] == "institute":
            render_institute_dashboard()
            return

        # Department -- the existing app, completely unchanged.
        with ui.row().classes("items-center justify-between w-full"):
            ui.label("MSBTE Result Tool").classes("text-lg font-semibold")
            dept = state["logged_in"]

            def do_logout():
                global REPORTS_DIR
                state["logged_in"] = None
                state["active_scheme"] = None
                state["scheme_group_called"] = False
                mt.set_active_scheme_db("msbte_data.db")
                mt.set_active_department_mapping_file("layout_mapping.json")
                REPORTS_DIR = "reports"
                mt.set_active_department_context("", "", "", "", "")
                reset_all_operational_modes()
                ui.navigate.reload()

            with ui.row().classes("items-center gap-3"):
                ui.label(f"{dept['department_name']}").classes("text-sm text-gray-600")
                ui.button("Logout", icon="logout", on_click=do_logout).props("outline dense")

        with ui.row().classes("w-full no-wrap items-start gap-4 p-4"):
            # ---------------- LEFT SIDEBAR ----------------
            with ui.column().classes("w-56 gap-2"):
                ui.label("Modes").classes("text-xs uppercase text-gray-500 tracking-wide")

                seating_key, seating_label, seating_icon = next(m for m in MODES if m[0] == "seating")
                btn = ui.button(
                    seating_label, icon=seating_icon, on_click=lambda: select_mode(seating_key)
                ).props("align=left unelevated").classes("w-full justify-start")
                mode_buttons[seating_key] = btn

                state["scheme_picker_container"] = ui.column().classes("w-full gap-1")
                state["scheme_entry_container"] = ui.column().classes("w-full gap-1")
                state["operational_modes_container"] = ui.column().classes("w-full gap-2")

            # ---------------- RIGHT PANEL ----------------
            with ui.column().classes("flex-grow gap-4 min-w-0"):
                top_container = ui.column().classes("w-full gap-0")
                content_container = ui.column().classes("w-full")

        render_scheme_picker(state["scheme_picker_container"])
        render_scheme_entry_buttons(state["scheme_entry_container"])
        render_operational_mode_buttons(state["operational_modes_container"])
        select_mode(state["mode"])


@ui.page("/")
def main_page():
    global page_container

    ui.add_head_html("<style>body { background: #f5f6f8; }</style>")
    # Every render_mode_content() call clears and rebuilds the DOM, which
    # normally resets scroll position to the top -- annoying mid-training
    # when a click causes a re-render. This listener remembers each
    # tracked container's scrollTop by id in a page-level JS object that
    # survives the rebuild (only the DOM element gets destroyed, not this
    # script); restore_scroll_positions() below puts it back afterward.
    # Capture phase is required since "scroll" doesn't bubble.
    ui.add_head_html("""
        <script>
        window.__scrollPos = window.__scrollPos || {};
        document.addEventListener('scroll', function(e) {
            if (e.target && e.target.id) { window.__scrollPos[e.target.id] = e.target.scrollTop; }
        }, true);
        </script>
    """)

    page_container = ui.column().classes("w-full")
    render_page_body()


ui.run(title="MSBTE Result Tool", port=8080, reload=False)
