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

mt.init_db(mt.DB_FILE)

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
        "semester": {"enabled": True, "status": "both"},
        "yearly_result": {"enabled": True, "status": "both"},
        "k7_partb": {"enabled": True, "status": "both", "fail_threshold": 30.0},
        "k7_partc": {"enabled": True, "status": "both"},
        "yearly_eligibility": {"enabled": True, "status": "both"},
        "topper_list": {"enabled": True, "status": "both"},
        "bright_weak": {"enabled": True, "status": "both", "weak_threshold": 40.0, "bright_threshold": 75.0},
    },

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

    # The Global Scheme Context's current selection -- None until the
    # user picks a radio button in the sidebar. Once set, mt.DB_FILE has
    # already been repointed at this scheme's database (see
    # select_active_scheme() below) -- this dict is purely for DISPLAY
    # (which radio button to show checked, what label to print) and for
    # Phase 3's gating check; nothing about it is passed into Train,
    # Extract, Course Codes, Recheck, Offline Import, or Report.
    "active_scheme": None,  # {"program", "year", "session", "scheme"} or None
    "scheme_picker_container": None,
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
    "auth_view": "login",   # "login" | "signup" | "verify" | "forgot"
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
    "verify_username": "",
    "verify_code": "",
    "forgot_recovery_email": "",

    # Institute Dashboard, Tile 1 (Generate Departments)
    "gen_dept_count": "",
    "gen_dept_fields": [],  # list of {"name": "", "username": "", "password": ""}, index-aligned
}

SEATING_COLUMN_SPECS = [
    ("enrollment", "Enrollment Number"),
    ("name", "Student Name"),
    ("seat", "Seat Number"),
    ("sem_scheme", "Semester-Scheme code (e.g. \"TX-4-K\")"),
    ("regular_ex", "Regular/EX (R or X)"),
    ("subjects", "Subject Appeared (comma-separated)"),
]

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


def finalize_training():
    mapping = state["train_mapping"]
    with open(mt.MAPPING_FILE, "w", encoding="utf-8") as f:
        json.dump(mapping, f, indent=2, ensure_ascii=False)

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


async def start_extraction():
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

    state["extract_step"] = "running"
    state["extract_log"] = []
    state["extract_summary"] = None
    render_mode_content()

    session = requests.Session()
    all_extracted = []
    all_canonical = []
    all_subjectwise = []
    all_review = []
    processed = 0
    skipped = 0

    for enr in enrollments:
        _log(f"Fetching {enr} ...", "extract_log")
        try:
            html, attempts = await web_fetch_result_html_with_retry(
                session, enr, log_key="extract_log"
            )
            if not html:
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
            all_canonical.extend(canonical_rows)
            all_subjectwise.extend(subjectwise_records)
            if attempts > 1:
                if extracted or canonical_rows or subjectwise_records:
                    _log(
                        f"  Resolved after {attempts} attempt(s) "
                        f"(earlier attempt(s) likely had a wrong captcha).",
                        "extract_log",
                    )
                else:
                    _log(
                        f"  Still no result tables after {attempts} attempts "
                        f"(wrong enrollment number, no result available, or "
                        f"repeated wrong captcha). Skipping.",
                        "extract_log",
                    )
            all_extracted.extend(extracted)
            all_review.extend(review)
            processed += 1
            _log(
                f"  {len(extracted)} field(s) + {len(subjectwise_records)} subject-wise mark(s) "
                f"extracted, {len(review)} flagged for review.",
                "extract_log",
            )
        except Exception as e:
            # One enrollment blowing up must never kill the rest of the
            # batch -- log it and move on to the next enrollment number.
            _log(f"  ERROR processing {enr}: {e}. Skipping and continuing.", "extract_log")
            all_review.append({
                "enrollment": enr, "semester_label": None,
                "reason": f"Unhandled error during extraction: {e}",
            })
            skipped += 1

    mt.save_records_to_db(all_extracted, all_review, mt.DB_FILE)
    mt.save_canonical_marks_to_db(all_canonical, mt.DB_FILE)
    mt.save_subjectwise_student_records_to_db(all_subjectwise, mt.DB_FILE)
    invalidate_downstream_data()

    state["extract_summary"] = {
        "total": len(enrollments),
        "processed": processed,
        "skipped": skipped,
        "extracted": len(all_extracted),
        "canonical": len(all_canonical),
        "subjectwise": len(all_subjectwise),
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
    render_mode_content()


def load_new_database():
    """'Load New Database' button -- clears the shared enrollment paste
    box so the user can type in a completely fresh list, without
    touching whatever's already saved in the database itself."""
    state["enrollment_text"] = ""
    state["extract_step"] = "idle"
    state["extract_log"] = []
    state["extract_summary"] = None
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
                ui.label("Successfully processed:")
                ui.label(str(summary.get("processed", 0))).classes("font-semibold")
                ui.label("Skipped / failed:")
                ui.label(str(summary.get("skipped", 0))).classes("font-semibold")
                ui.label("Identity/summary fields extracted (K-scheme):")
                ui.label(str(summary.get("extracted", 0))).classes("font-semibold")
                ui.label("Identity/summary rows extracted (I-scheme):")
                ui.label(str(summary.get("canonical", 0))).classes("font-semibold")
                ui.label("Subject-wise marks extracted:")
                ui.label(str(summary.get("subjectwise", 0))).classes("font-semibold")
                ui.label("Flagged for review:")
                ui.label(str(summary.get("review", 0))).classes(
                    "font-semibold" + (" text-orange-600" if summary.get("review") else "")
                )
            ui.label(
                "A semester trained only through the subject-wise wizard (not the flat "
                "range-selector) is expected to show 0 for whichever of the two "
                "identity/summary rows above doesn't match its scheme -- that's normal, not a "
                "failure."
            ).classes("text-xs text-gray-500 mt-1")

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

    try:
        if sel["semester"]["enabled"]:
            for sem_label in semesters_in_db:
                _report_log(f"Building {sem_label.title()} report...")
                _collect(f"{sem_label.title()} Report", _generate_and_collect(
                    f"{sem_label.title()} Report", mt.generate_semester_pdf,
                    sem_label, mt.DB_FILE, student_status=sel["semester"]["status"],
                ))

        if sel["yearly_result"]["enabled"]:
            _report_log("Building Yearly Result report...")
            _collect("Yearly Result Report", _generate_and_collect(
                "Yearly Result Report", mt.generate_yearly_result_pdf,
                mt.DB_FILE, student_status=sel["yearly_result"]["status"],
                include_yearly_block=not simple_yearly_mode,
            ))

        if sel["k7_partb"]["enabled"]:
            _report_log("Building K7 (Part B) report...")
            _collect("K7 (Part B) Report", _generate_and_collect(
                "K7 (Part B) Report", mt.generate_k7_partb_pdf,
                mt.DB_FILE, student_status=sel["k7_partb"]["status"], semesters=semesters_in_db,
                fail_pct_threshold=sel["k7_partb"]["fail_threshold"],
            ))

        if sel["k7_partc"]["enabled"]:
            _report_log("Building K7 (Part C) report...")
            _collect("K7 (Part C) Report", _generate_and_collect(
                "K7 (Part C) Report", mt.generate_k7_partc_pdf,
                mt.DB_FILE, student_status=sel["k7_partc"]["status"], semesters=semesters_in_db,
            ))

        if sel["yearly_eligibility"]["enabled"] and not simple_yearly_mode:
            _report_log("Building Yearly Eligible/Non-Eligible list...")
            _collect("Yearly Eligible/Non-Eligible List", _generate_and_collect(
                "Yearly Eligible/Non-Eligible List", mt.generate_yearly_eligibility_pdf,
                mt.DB_FILE, student_status=sel["yearly_eligibility"]["status"],
            ))

        if sel["topper_list"]["enabled"]:
            _report_log("Building Topper List...")
            _collect("Semesterwise and Yearly Topper List", _generate_and_collect(
                "Semesterwise and Yearly Topper List", mt.generate_topper_list_pdf,
                mt.DB_FILE, student_status=sel["topper_list"]["status"],
            ))

        if sel["bright_weak"]["enabled"]:
            _report_log("Building Bright/Weak Student List...")
            _collect("Semester wise Bright/Weak Student List", _generate_and_collect(
                "Semester wise Bright/Weak Student List", mt.generate_bright_weak_pdf,
                mt.DB_FILE, student_status=sel["bright_weak"]["status"],
                weak_threshold=sel["bright_weak"]["weak_threshold"],
                bright_threshold=sel["bright_weak"]["bright_threshold"],
            ))
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
            ui.label(REPORT_ROW_LABELS[key]).classes("text-sm font-medium")
            if blocked:
                ui.icon("warning", color="negative").classes("text-sm")

        ui.icon("expand_more" if not is_open else "expand_less").classes(
            "text-lg cursor-pointer"
        ).on("click", lambda k=key: toggle_report_panel(k))


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

    def on_status(e, k=key):
        state["report_selection"][k]["status"] = e.value

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
            ui.radio(
                REPORT_STATUS_OPTIONS, value=sel["status"], on_change=on_status,
            ).props("dense").classes("text-xs")

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
                        ui.label(REPORT_ROW_LABELS[key]).classes("text-base font-bold")
                        ui.button(
                            icon="close", on_click=lambda k=key: toggle_report_panel(k),
                        ).props("flat dense round size=sm")
                    ui.separator().classes("mb-2")
                    render_report_panel_content(key)


def render_report_select(container):
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
    if mode in MODE_ORDER + ["report"] and state["active_scheme"] is None:
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


SCROLL_TRACKED_IDS = ["trainer-sidebar-scroll", "trainer-grid-scroll"]


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


def confirm_wipe_seating_chart():
    def do_wipe():
        dialog.close()
        count = mt.wipe_seating_chart_data(mt.SEATING_DB_FILE)
        state["seating_columns"] = {k: "" for k, _ in SEATING_COLUMN_SPECS}
        state["seating_parsed_rows"] = None
        state["seating_parse_errors"] = []
        state["seating_last_saved_count"] = None
        state["seating_last_save_errors"] = []
        ui.notify(f"Deleted {count} seating chart row(s) from the database.", type="positive")
        render_mode_content()

    with ui.dialog() as dialog, ui.card():
        ui.label("Delete ALL seating chart data?").classes("text-md font-bold text-red-700")
        ui.label(
            "This permanently removes every seating chart row for every "
            "semester from the database. It does not touch student result "
            "data (Train/Extract/CSV Import/Recheck)."
        ).classes("text-sm mt-1")
        with ui.row().classes("gap-2 mt-4"):
            ui.button("Delete Everything", icon="delete_forever", on_click=do_wipe).props(
                "unelevated color=negative"
            )
            ui.button("Cancel", on_click=dialog.close).props("outline")
    dialog.open()


def select_active_scheme(decl):
    """The one place a sidebar radio pick actually takes effect. Repoints
    mt.DB_FILE at this scheme's database (via mt.set_active_scheme_db) --
    from this point on, every mode's calls into msbte_tool.py (which all
    already pass db_path=mt.DB_FILE) transparently read/write this
    scheme's data, with none of those modes' own code knowing a switch
    happened. `decl` is one entry from mt.list_all_scheme_declarations():
    {"program", "year", "session", "scheme"}.

    Also invalidates any in-memory cache that was loaded FROM the
    previous scheme's database and would otherwise silently keep
    showing after the switch -- currently just Course Codes'
    load-once-per-render-cycle cache (state["coursecode_data"]; see
    load_coursecode_data()). Every other mode already re-queries
    mt.DB_FILE fresh on each render, so nothing else needs clearing.
    """
    path = mt.scheme_db_path(decl["institute"], decl["program"], decl["year"], decl["session"], decl["scheme"])
    mt.ensure_scheme_db(decl["institute"], decl["program"], decl["year"], decl["session"], decl["scheme"])
    mt.set_active_scheme_db(path)
    state["active_scheme"] = decl
    state["coursecode_data"] = None


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
    with container:
        dept = state["logged_in"]
        declarations = mt.list_all_scheme_declarations(
            dept["institute_name"], dept["department_name"], mt.SEATING_DB_FILE,
        )
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
            render_operational_mode_buttons(state["operational_modes_container"])
            render_mode_content()

        with ui.card().classes("w-full border-2 border-primary").style("padding: 6px 10px;"):
            ui.label("Active Scheme").classes("text-xs font-bold uppercase text-primary")
            ui.radio(
                list(options.keys()), value=current_label, on_change=on_pick,
            ).props("dense")


def render_operational_mode_buttons(container):
    """The Global Scheme Group's own buttons -- Train, Extract, Course
    Codes, Offline Import, Recheck, Report. Deliberately absent from the
    sidebar entirely (not just walled/disabled) until a scheme is
    active: this group is a CONTEXT-DEPENDENT layer, not a standing part
    of the sidebar the way Seating Chart is. Rebuilt in place whenever
    the active scheme changes (see render_scheme_picker's on_pick)."""
    if container is None:
        return
    container.clear()
    if state["active_scheme"] is None:
        return
    with container:
        for key, label, icon in MODES:
            if key == "seating":
                continue
            btn = ui.button(
                label, icon=icon, on_click=lambda k=key: select_mode(k)
            ).props("align=left unelevated").classes("w-full justify-start")
            mode_buttons[key] = btn


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
            ui.label(
                "Year / Session -- describes THIS exam sitting, used with your department's "
                "name (below) to name the database file each scheme below gets saved into."
            ).classes("text-xs text-gray-500")
            with ui.row().classes("w-full gap-3 items-center"):
                dept = state["logged_in"]
                ui.input(label="Department", value=dept["department_name"]).classes("flex-1").props(
                    "outlined dense readonly"
                )

                def on_paste_year(e):
                    state["seating_paste_year"] = e.value

                def on_paste_session(e):
                    state["seating_paste_session"] = e.value

                ui.input(label="Year", value=state["seating_paste_year"],
                          on_change=on_paste_year).classes("flex-1").props("outlined dense")
                ui.select(["Odd", "Even"], label="Session", value=state["seating_paste_session"],
                           on_change=on_paste_session).classes("flex-1").props("outlined dense")
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

                    saved, errors = mt.save_seating_chart_rows(state["seating_parsed_rows"], mt.SEATING_DB_FILE)
                    state["seating_last_saved_count"] = saved
                    state["seating_last_save_errors"] = errors

                    # Every scheme now present in the seating chart gets its
                    # own database created (idempotent -- an already-created
                    # scheme's database is left untouched), named from this
                    # department's Institute/Program plus this paste path's
                    # own Year/Session.
                    schemes_now = mt.list_active_schemes(mt.SEATING_DB_FILE)
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
                    render_scheme_picker(state["scheme_picker_container"])

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

        summary = mt.get_seating_chart_summary(mt.SEATING_DB_FILE)
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
                for sem in scheme_data["by_semester"]:
                    with ui.expansion(
                        f"{sem['semester_label']}    Regular: {sem['regular_count']}   "
                        f"EX: {sem['ex_count']}   Total: {sem['total_count']}"
                    ).classes("w-full border-b"):
                        with ui.row().classes("w-full gap-6"):
                            with ui.column().classes("flex-1"):
                                ui.label(f"Regular students ({sem['regular_count']})").classes(
                                    "text-xs font-semibold text-gray-600"
                                )
                                for s in sem["regular_students"]:
                                    ui.label(f"{s['enrollment']}  --  {s['student_name']}  (Seat {s['seat_number']})").classes(
                                        "text-xs"
                                    )
                            with ui.column().classes("flex-1"):
                                ui.label(f"EX students ({sem['ex_count']})").classes(
                                    "text-xs font-semibold text-gray-600"
                                )
                                for s in sem["ex_students"]:
                                    ui.label(f"{s['enrollment']}  --  {s['student_name']}  (Seat {s['seat_number']})").classes(
                                        "text-xs"
                                    )

                gt = scheme_data["grand_total"]
                ui.label(f"All Semesters ({scheme}) Combined").classes("text-md font-semibold mt-3")
                ui.label(f"Regular: {gt['regular_count']}      EX: {gt['ex_count']}      Total: {gt['total_count']}").classes(
                    "text-sm mt-1"
                )
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
                cover = mt.compute_train_sample_enrollments(scheme, mt.SEATING_DB_FILE)
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
        with ui.row().classes("w-full gap-3 items-center"):
            dept = state["logged_in"]
            ui.input(label="Department", value=dept["department_name"]).classes("flex-1").props(
                "outlined dense readonly"
            )

            def on_manual_year(e):
                state["seating_manual_year"] = e.value

            def on_manual_session(e):
                state["seating_manual_session"] = e.value

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
                render_scheme_picker(state["scheme_picker_container"])

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

    if mode in MODE_ORDER + ["report"] and state["active_scheme"] is None:
        with content_container:
            with ui.card().classes("w-full border-2 border-orange-300"):
                ui.label("No scheme selected").classes("text-lg font-bold text-orange-700")
                ui.label(
                    "This mode needs an active scheme to know which database to work "
                    "against. Go to Seating Chart, declare or detect a scheme (via paste "
                    "or manual entry), then pick it in the sidebar's Active Scheme list."
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
            "A verification code will be sent to your recovery email -- you'll need it "
            "on the next screen before you can log in."
        ).classes("text-xs text-gray-500 mt-2")

        def do_signup():
            name = state["signup_institute_name"].strip()
            username = state["signup_username"].strip()
            password = state["signup_password"]
            email = state["signup_recovery_email"].strip()
            if not name or not username or not password or not email:
                ui.notify("Fill in every field first.", type="warning")
                return
            ok, err = mt.sign_up_institute(name, username, password, email)
            if not ok:
                ui.notify(err, type="negative")
                return
            state["verify_username"] = username
            state["auth_view"] = "verify"
            ui.notify("Account created -- check your recovery email for the code.", type="positive")
            render_page_body()

        ui.button("Sign Up", icon="how_to_reg", on_click=do_signup).classes("w-full mt-3").props(
            "unelevated color=primary"
        )

        def back_to_login():
            state["auth_view"] = "login"
            render_page_body()

        ui.link("Back to Login", "#").on("click", back_to_login).classes("text-sm mt-2")


def render_verify_screen():
    ui.label("Verify Your Email").classes("text-2xl font-bold mt-8")
    with ui.card().classes("w-96 mt-4"):
        ui.label(f"Enter the 6-digit code sent to your recovery email.").classes("text-sm text-gray-600")

        def on_username(e):
            state["verify_username"] = e.value

        def on_code(e):
            state["verify_code"] = e.value

        ui.input(label="Username", value=state["verify_username"],
                  on_change=on_username).classes("w-full mt-2").props("outlined dense")
        ui.input(label="Verification Code", value=state["verify_code"],
                  on_change=on_code).classes("w-full mt-2").props("outlined dense maxlength=6")

        def do_verify():
            ok, err = mt.verify_institute_email(state["verify_username"].strip(), state["verify_code"].strip())
            if not ok:
                ui.notify(err, type="negative")
                return
            ui.notify("Verified! You can log in now.", type="positive")
            state["auth_view"] = "login"
            state["login_institute_username"] = state["verify_username"]
            render_page_body()

        ui.button("Verify", icon="check_circle", on_click=do_verify).classes("w-full mt-3").props(
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
            "If a verified account is found, your username and password will be emailed to "
            "this address."
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
            ui.navigate.reload()

        ui.button("Logout", icon="logout", on_click=do_logout).props("outline")

    with ui.row().classes("w-full gap-4 mt-4 items-start flex-wrap"):
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
                ui.label("Existing departments (for admin reference):").classes("text-sm font-semibold")
                for d in existing:
                    ui.label(f"{d['department_name']} -- username: {d['username']}, password: {d['password']}").classes(
                        "text-xs text-gray-600"
                    )

        # ---------------- TILE 2: Practical Time Table (placeholder) ----------------
        with ui.card().classes("w-72"):
            ui.label("Generate Practical Time Table").classes("text-lg font-bold")
            ui.label("For all departments. Functionality coming later.").classes("text-xs text-gray-500 mt-1")
            ui.button("Generate", icon="event_note").props("outline").classes("mt-3").disable()

        # ---------------- TILE 3: Online Theory Time Table (placeholder) ----------------
        with ui.card().classes("w-72"):
            ui.label("Online Theory Time Table").classes("text-lg font-bold")
            ui.label("For all departments. Functionality coming later.").classes("text-xs text-gray-500 mt-1")
            ui.button("Generate", icon="schedule").props("outline").classes("mt-3").disable()


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
                elif view == "verify":
                    render_verify_screen()
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
                state["logged_in"] = None
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
                state["operational_modes_container"] = ui.column().classes("w-full gap-2")

            # ---------------- RIGHT PANEL ----------------
            with ui.column().classes("flex-grow gap-4"):
                top_container = ui.column().classes("w-full gap-0")
                content_container = ui.column().classes("w-full")

        render_scheme_picker(state["scheme_picker_container"])
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
