"""
msbte_tool.py

Single-file MSBTE result tool. Three modes:

  python msbte_tool.py train
      Interactive one-time training. Prompts for up to 6 sample
      enrollment numbers (blank = skip), fetches each live (you solve
      the captcha manually each time, exactly like the existing
      scraper), auto-detects which semester(s) each result covers,
      cross-checks table shapes whenever two enrollments cover the same
      semester, then lets you tick checkboxes for which rows to keep
      per semester. Saves layout_mapping.json, and saves that semester's
      heading facts (subjects/THPRSLA/FASA/maximum_marks) to the database.

  python msbte_tool.py extract
      Reads enrollment numbers (one per line, top to bottom, STOPPING at
      the first blank line) from enrollment_list.txt, fetches each live
      (captcha manual again), applies layout_mapping.json, and saves the
      per-student data (identity fields, obtained_marks, summary fields)
      to the database. One enrollment failing doesn't stop the batch --
      it's logged for review and extraction moves on to the next line.

  python msbte_tool.py report
      Builds one print-ready PDF report per semester, straight from the
      database -- no fetching, no captchas needed. Also builds
      "Yearly_Result_Report.pdf", a cross-semester report (one row per
      enrollment, one 5-column block per semester: Total Marks/Obtained
      Total/Percentage/Result/Failed Subjects); "K7_PartB_Report.pdf", a
      subject/THPRSLA-component/FASA-column statistics report (lowest/
      highest/appeared/pass/above-60%/failed marks, per faculty) with one
      section per semester; "K7_PartC_Report.pdf", the FA-TH vs SA-TH
      Score Index comparison (one row per Theory subject, Difference
      highlighted above 20%); and "Yearly_Eligible_NonEligible_Report.pdf",
      one Sr.No./Enrollment No/Name/Program/Eligible-Non-Eligible list per
      academic year (same Eligible/Non-Eligible-for-Next-Year call the
      Yearly Result report makes, Eligible enrollments listed before Not
      Eligible). Asks (checkbox dialog) which report(s) to build and
      whether to include Regular students, EX students, or both (each
      report's status is independent).

  python msbte_tool.py recheck
      For students whose marks/Result changed after applying for
      rechecking. Asks Automatic (re-fetch the live result from MSBTE,
      same captcha flow as extract mode, for every enrollment listed in
      recheck_list.txt -- but flags any enrollment where nothing actually
      changed, since MSBTE may not have updated their site yet) or Manual
      (type the corrected marks in yourself, one enrollment at a time, in
      a form pre-filled with the current database values, semester by
      semester). Either way the correction overwrites the existing
      student_records rows in place.

  python msbte_tool.py coursecodes
      Opens an Excel-style dialog listing every semester's subjects (from
      train mode), prefilled with any Abbreviation/Course Code/faculty
      entered previously -- fill in/edit per subject and save. Faculty is
      entered per THPRSLA component (Theory Faculty / Practicals Faculty /
      SLA Faculty, whichever apply to that subject), since theory and
      practicals can be taught by different people -- this is what a
      future faculty-wise report would group by.
      Supports bulk paste: copy a block of cells from Excel and paste
      into any cell here to fill across columns and down rows at once.
      Re-running this any time (even after data's already been extracted
      and reports built) is totally fine -- it reopens prefilled with
      whatever's saved, ready to edit and save again.
      Purely a manual data-entry step; doesn't fetch or touch reports.

Design principles (per project requirements):
  - NOTHING about table position/order is hardcoded as "column X always
    means Y". Column/row meaning is entirely learned during Train mode
    by YOU ticking checkboxes against the real page, not guessed.
  - Every semester's tables are grouped in runs of 4
    (header_info, marks, summary, instructions) -- this pattern itself
    is the one structural assumption the tool makes about MSBTE's page,
    same as your original scraper.
  - Row/column shape is validated before every extraction. A shape
    mismatch never silently produces wrong data -- it's flagged for
    review instead.
  - All data lives in the database (msbte_data.db); reports are built
    directly from it as PDFs. No Excel/CSV anywhere in this pipeline.
"""

import sys
import os
import re
import json
import sqlite3
import random
import string
import smtplib
from email.message import EmailMessage

import requests
from bs4 import BeautifulSoup

try:
    import tkinter as tk
    from tkinter import ttk, messagebox
    import tkinter.font as tkfont
    from PIL import Image, ImageTk
except ImportError:
    # tkinter isn't available in every environment this module gets
    # imported in (e.g. the NiceGUI web app never uses the tkinter
    # dialogs below -- app.py replaces them with in-browser equivalents).
    # Only the tkinter-specific dialog/popup functions need these names;
    # everything else in this module works fine without them.
    tk = ttk = messagebox = tkfont = Image = ImageTk = None


# ==========================================================
# CONSTANTS
# ==========================================================

MSBTE_URL = "https://result.msbte.ac.in/pcwebBTRes/pcResult01/pcfrmViewMSBTEResult.aspx"
MAPPING_FILE = "layout_mapping.json"
ENROLLMENT_LIST_FILE = "enrollment_list.txt"
RECHECK_LIST_FILE = "recheck_list.txt"
DB_FILE = "msbte_data.db"
CAPTCHA_IMG = "captcha.png"

# The Seating Chart's own database -- ALWAYS this one fixed file,
# regardless of which scheme is currently active (see the Global Scheme
# Context section below). DB_FILE, in contrast, gets repointed at a
# different per-scheme file every time the user switches schemes.
# Seating Chart data is never scheme-scoped -- it's the shared source
# that scheme detection itself comes from -- so it can't live inside
# any one scheme's own database.
SEATING_DB_FILE = "seating_chart.db"

# The multi-tenant authentication database -- another fixed, shared file
# (same pattern as SEATING_DB_FILE), since login has to work before any
# institute, department, or scheme context exists at all.
AUTH_DB_FILE = "auth.db"

# --- SMTP configuration for outgoing account emails (verification codes,
# forgot-username/password) -- FILL THESE IN with real values before
# email sending will actually work. Left blank, send_email() below will
# raise a clear error rather than silently failing, so a missing
# configuration is obvious immediately rather than discovered later. ---
SMTP_HOST = "smtp.gmail.com"            # e.g. "smtp.gmail.com"
SMTP_PORT = 587           # 587 = STARTTLS (most common), 465 = SSL
SMTP_USERNAME = "prashantjinde@gmail.com"        # the SENDING account's login (often same as SMTP_FROM)
SMTP_PASSWORD = "qqxbcmaupmvjjfmq"        # an app password, NOT the account's normal login password
SMTP_FROM = "prashantjinde@gmail.com"            # the "From:" address shown to recipients

# ------------------------------------------------------------------
# Runtime logging for Render
# ------------------------------------------------------------------
import logging

logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s | %(levelname)s | %(name)s | %(message)s",
)
logger = logging.getLogger("msbte_tool")


# ==========================================================
# AUTHENTICATION -- multi-tenant: each Institute signs up independently,
# creates its own Departments, and Departments log in scoped to their
# owning Institute (see authenticate_department()'s three-field lookup).
# Both tables live in AUTH_DB_FILE, never anywhere scheme/department-
# scoped, for the same reason SEATING_DB_FILE is separate from DB_FILE:
# this data has to exist and be readable before any of that context
# does.
# ==========================================================

def init_auth_db(db_path=AUTH_DB_FILE):
    """Create the auth database (if it doesn't exist yet) and its two
    tables. Idempotent -- CREATE TABLE IF NOT EXISTS means calling this
    repeatedly is always safe.
    """
    conn = sqlite3.connect(db_path)
    conn.execute("""
        CREATE TABLE IF NOT EXISTS institutes (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            institute_name TEXT NOT NULL,
            username TEXT NOT NULL UNIQUE,     -- email-format login identifier
            password TEXT NOT NULL,
            recovery_email TEXT NOT NULL,
            email_verified INTEGER NOT NULL DEFAULT 0,
            verification_code TEXT             -- pending code; cleared once verified
        )
    """)
    conn.execute("""
        CREATE TABLE IF NOT EXISTS departments (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            institute_id INTEGER NOT NULL,
            department_name TEXT NOT NULL,
            username TEXT NOT NULL UNIQUE,     -- globally unique across EVERY institute
            password TEXT NOT NULL,
            FOREIGN KEY (institute_id) REFERENCES institutes(id)
        )
    """)
    conn.commit()
    conn.close()


def _generate_verification_code():
    """A 6-digit numeric code, emailed to the recovery address at sign-up
    time -- entered on a verification screen before the account can log
    in at all. Zero-padded so it's always exactly 6 digits."""
    return f"{random.randint(0, 999999):06d}"


def send_email(to_address, subject, body):
    """Send a plain-text email via SMTP with Render-visible diagnostics."""
    logger.info(
        "SMTP: start | host=%s | port=%s | from=%s | to=%s | subject=%s",
        SMTP_HOST or "<EMPTY>", SMTP_PORT, SMTP_FROM or "<EMPTY>",
        to_address or "<EMPTY>", subject
    )

    if not SMTP_HOST or not SMTP_FROM:
        logger.error(
            "SMTP: incomplete configuration | host=%r | username=%r | "
            "from=%r | password_configured=%s",
            SMTP_HOST, SMTP_USERNAME, SMTP_FROM, bool(SMTP_PASSWORD)
        )
        raise RuntimeError(
            "Email sending isn't configured yet -- fill in SMTP_HOST, "
            "SMTP_USERNAME, SMTP_PASSWORD, and SMTP_FROM in msbte_tool.py "
            "before sign-up/forgot-password emails can be sent."
        )

    msg = EmailMessage()
    msg["Subject"] = subject
    msg["From"] = SMTP_FROM
    msg["To"] = to_address
    msg.set_content(body)

    try:
        logger.info("SMTP: connecting to %s:%s", SMTP_HOST, SMTP_PORT)

        if SMTP_PORT == 465:
            with smtplib.SMTP_SSL(SMTP_HOST, SMTP_PORT, timeout=20) as server:
                logger.info("SMTP: SSL connection established")
                if SMTP_USERNAME:
                    logger.info("SMTP: authenticating as %s", SMTP_USERNAME)
                    server.login(SMTP_USERNAME, SMTP_PASSWORD)
                    logger.info("SMTP: authentication successful")
                server.send_message(msg)
        else:
            with smtplib.SMTP(SMTP_HOST, SMTP_PORT, timeout=20) as server:
                logger.info("SMTP: TCP connection established")
                logger.info("SMTP: starting TLS")
                server.starttls()
                logger.info("SMTP: TLS established")
                if SMTP_USERNAME:
                    logger.info("SMTP: authenticating as %s", SMTP_USERNAME)
                    server.login(SMTP_USERNAME, SMTP_PASSWORD)
                    logger.info("SMTP: authentication successful")
                server.send_message(msg)

        logger.info("SMTP: email sent successfully")

    except Exception:
        logger.exception("SMTP: email send FAILED")
        raise


def sign_up_institute(institute_name, username, password, recovery_email, db_path=AUTH_DB_FILE):
    """Creates a new, UNVERIFIED institute account and emails a 6-digit
    verification code to recovery_email. The account cannot log in (see
    authenticate_institute()) until verify_institute_email() confirms
    that code.

    Returns (True, None) on success, or (False, error_message) if the
    username is already taken (checked globally -- institute usernames
    and department usernames never collide with each other either,
    since institute login and department login must always be tellable
    apart) or if sending the verification email fails.
    """
    logger.info(
        "SIGNUP: start | institute=%r | username=%r | recovery_email=%r | db=%s",
        institute_name, username, recovery_email, db_path
    )
    logger.info("SIGNUP: initializing auth database")
    init_auth_db(db_path)
    logger.info("SIGNUP: auth database initialized")

    conn = sqlite3.connect(db_path)
    existing = conn.execute(
        "SELECT 1 FROM institutes WHERE username = ? UNION SELECT 1 FROM departments WHERE username = ?",
        (username, username),
    ).fetchone()
    if existing:
        conn.close()
        return False, "That username is already taken."

    code = _generate_verification_code()
    conn.execute(
        "INSERT INTO institutes (institute_name, username, password, recovery_email, "
        "email_verified, verification_code) VALUES (?, ?, ?, ?, 0, ?)",
        (institute_name, username, password, recovery_email, code),
    )
    conn.commit()
    conn.close()
    logger.info("SIGNUP: account inserted successfully | username=%r", username)

    try:
        logger.info("SIGNUP: sending verification email | username=%r", username)
        send_email(
            recovery_email, "Verify your MSBTE Result Tool account",
            f"Your verification code is: {code}\n\n"
            f"Enter this code on the sign-up screen to activate your account.",
        )
    except Exception as e:
        logger.exception(
            "SIGNUP: verification email FAILED | username=%r | error=%s",
            username, e
        )
        return False, f"Account created, but the verification email failed to send: {e}"

    logger.info("SIGNUP: completed successfully | username=%r", username)
    return True, None


def verify_institute_email(username, code, db_path=AUTH_DB_FILE):
    """Confirms a sign-up verification code. Returns (True, None) and
    marks the account verified (clearing the stored code) on a match;
    (False, error_message) otherwise -- wrong code, or nothing pending
    for this username at all.
    """
    conn = sqlite3.connect(db_path)
    row = conn.execute(
        "SELECT verification_code, email_verified FROM institutes WHERE username = ?", (username,)
    ).fetchone()
    if row is None:
        conn.close()
        return False, "No account found for that username."
    stored_code, already_verified = row
    if already_verified:
        conn.close()
        return True, None  # idempotent -- re-verifying an already-verified account is a no-op success
    if code != stored_code:
        conn.close()
        return False, "That code doesn't match."
    conn.execute(
        "UPDATE institutes SET email_verified = 1, verification_code = NULL WHERE username = ?", (username,)
    )
    conn.commit()
    conn.close()
    return True, None


def authenticate_institute(username, password, db_path=AUTH_DB_FILE):
    """Checks Institute login credentials. Returns a dict {"id",
    "institute_name", "username", "recovery_email"} on success, or
    (None, error_message) on failure -- distinguishing "wrong password",
    "no such account", and "account not verified yet" so the login
    screen can show the right message.
    """
    conn = sqlite3.connect(db_path)
    conn.row_factory = sqlite3.Row
    row = conn.execute("SELECT * FROM institutes WHERE username = ?", (username,)).fetchone()
    conn.close()
    if row is None:
        return None, "No account found for that username."
    if not row["email_verified"]:
        return None, "This account hasn't been verified yet -- check your recovery email for the code."
    if row["password"] != password:
        return None, "Incorrect password."
    return {
        "id": row["id"], "institute_name": row["institute_name"],
        "username": row["username"], "recovery_email": row["recovery_email"],
    }, None


def change_institute_credentials(institute_id, new_username=None, new_password=None, db_path=AUTH_DB_FILE):
    """Updates an Institute's username and/or password (pass only the
    ones being changed; None leaves that field untouched). Returns
    (True, None) on success, or (False, error_message) if the new
    username is already taken by someone else (institute or department).
    """
    conn = sqlite3.connect(db_path)
    if new_username is not None:
        clash = conn.execute(
            "SELECT 1 FROM institutes WHERE username = ? AND id != ? "
            "UNION SELECT 1 FROM departments WHERE username = ?",
            (new_username, institute_id, new_username),
        ).fetchone()
        if clash:
            conn.close()
            return False, "That username is already taken."
        conn.execute("UPDATE institutes SET username = ? WHERE id = ?", (new_username, institute_id))
    if new_password is not None:
        conn.execute("UPDATE institutes SET password = ? WHERE id = ?", (new_password, institute_id))
    conn.commit()
    conn.close()
    return True, None


def forgot_institute_credentials(recovery_email, db_path=AUTH_DB_FILE):
    """Looks up the (verified) institute account matching recovery_email
    and emails back its REAL, currently-stored username and password
    as-is (no temporary/reset password -- see the project decision on
    this). Returns (True, None) on success, or (False, error_message) if
    no matching verified account exists or sending fails.
    """
    conn = sqlite3.connect(db_path)
    conn.row_factory = sqlite3.Row
    row = conn.execute(
        "SELECT * FROM institutes WHERE recovery_email = ? AND email_verified = 1", (recovery_email,)
    ).fetchone()
    conn.close()
    if row is None:
        return False, "No verified account found for that recovery email."
    try:
        send_email(
            recovery_email, "Your MSBTE Result Tool account details",
            f"Institute: {row['institute_name']}\n"
            f"Username: {row['username']}\n"
            f"Password: {row['password']}",
        )
    except Exception as e:
        return False, f"Found the account, but the email failed to send: {e}"
    return True, None


def create_department(institute_id, department_name, username, password, db_path=AUTH_DB_FILE):
    """Creates one Department under the given institute. Returns (True,
    None) on success, or (False, error_message) if the username is
    already taken -- checked GLOBALLY, across every institute's
    departments AND every institute's own login, since Department login
    (see authenticate_department()) needs every department username to
    be unambiguous on its own.
    """
    conn = sqlite3.connect(db_path)
    existing = conn.execute(
        "SELECT 1 FROM departments WHERE username = ? UNION SELECT 1 FROM institutes WHERE username = ?",
        (username, username),
    ).fetchone()
    if existing:
        conn.close()
        return False, f"Username '{username}' is already taken."
    conn.execute(
        "INSERT INTO departments (institute_id, department_name, username, password) VALUES (?, ?, ?, ?)",
        (institute_id, department_name, username, password),
    )
    conn.commit()
    conn.close()
    return True, None


def list_departments_for_institute(institute_id, db_path=AUTH_DB_FILE):
    """Every department this institute has generated, WITH their
    credentials visible -- this is what Tile 1 shows after generating,
    and what an institute admin reads from to relay a forgotten
    department username/password (see the project's stated department-
    recovery approach: the institute admin looks it up here and tells
    the department user directly, rather than a separate self-service
    department recovery flow).

    Returns a list of dicts: {"id", "department_name", "username", "password"}.
    """
    conn = sqlite3.connect(db_path)
    conn.row_factory = sqlite3.Row
    rows = conn.execute(
        "SELECT id, department_name, username, password FROM departments "
        "WHERE institute_id = ? ORDER BY id",
        (institute_id,),
    ).fetchall()
    conn.close()
    return [dict(r) for r in rows]


def authenticate_department(institute_name, username, password, db_path=AUTH_DB_FILE):
    """Checks Department login credentials -- three fields, since
    Department usernames alone (while globally unique) still need the
    Institute Name to confirm the login is happening against the right
    institute, not just guessing a valid username/password pair that
    happens to belong to someone else's department.

    Returns a dict {"id", "institute_id", "institute_name",
    "department_name", "username"} on success, or (None, error_message)
    on failure. institute_name is included specifically so callers (see
    app.py's Seating Chart Program-field wiring) don't need a separate
    lookup just to get the institute's name for database naming.
    """
    conn = sqlite3.connect(db_path)
    conn.row_factory = sqlite3.Row
    row = conn.execute("""
        SELECT departments.*, institutes.institute_name AS parent_institute_name
        FROM departments JOIN institutes ON departments.institute_id = institutes.id
        WHERE departments.username = ?
    """, (username,)).fetchone()
    conn.close()
    if row is None:
        return None, "No department found for that username."
    if row["parent_institute_name"] != institute_name:
        return None, "That username doesn't belong to this institute."
    if row["password"] != password:
        return None, "Incorrect password."
    return {
        "id": row["id"], "institute_id": row["institute_id"], "institute_name": row["parent_institute_name"],
        "department_name": row["department_name"], "username": row["username"],
    }, None


# ==========================================================
# GLOBAL SCHEME CONTEXT
# ==========================================================
# Train, Extract, Course Codes, Recheck, Offline Import, and Report are
# all "scheme-agnostic workers": none of their own code knows or asks
# which scheme it's operating on. Instead, every one of those modules'
# database calls already takes (or defaults to) DB_FILE -- so the ENTIRE
# mechanism for scoping their work to one scheme is: reassign what
# DB_FILE currently points at. Nothing else about those modules changes.
#
# Seating Chart is the one place that DOES know about scheme -- it's
# where schemes are discovered (see list_active_schemes(), which reads
# SEATING_DB_FILE, never DB_FILE) and where the user picks which one is
# currently active. That selection is what drives set_active_scheme_db()
# below.
#
# Each scheme gets its own database file, named from four pieces of
# context typed/chosen once in Seating Chart -- Program, Year, Session
# (Odd/Even), and the scheme letter itself (auto-detected from the
# pasted seating chart data, never typed):
#   <base_dir>/<Program>/<Year>/<Session>/<Scheme>.db
# e.g. "DTM/2025_2026/odd/K.db".

def sanitize_path_component(value):
    """Turns one piece of free-typed context (Program, Year, or Session)
    into a safe, readable path segment: trims whitespace, then collapses
    any run of '-' or whitespace into a single '_' -- so "2025-2026",
    "2025 2026", and "2025_2026" all normalize to the identical
    "2025_2026" (meaning the same academic year always resolves to the
    same database file, no matter which of those the user happened to
    type). The scheme letter itself needs no such normalization (it's
    auto-detected, always a single clean letter like "K" or "I"), but
    passing it through here too is harmless and keeps every path
    segment held to the same rule.
    """
    value = (value or "").strip()
    value = re.sub(r"[-\s]+", "_", value)
    return value


def scheme_db_path(institute, program, year, session, scheme, base_dir="."):
    """Computes (but does not create) the database file path for one
    scheme, given the five pieces of context. Pure function -- no
    filesystem access; see ensure_scheme_db() for the version that
    actually creates the file.

    `institute` sits above `program` (in practice, a logged-in
    department's name) so two different institutes can each have a
    department with the same name without colliding -- e.g.
    "ABC_Polytechnic/Computer_Engineering/..." vs
    "XYZ_Institute/Computer_Engineering/...".

    Session is always lowercased in the resulting path ("Odd"/"Even" ->
    "odd"/"even") regardless of how it's displayed in the UI dropdown --
    matches the original naming example (e.g. "DTM/2025_2026/odd/K.db").
    Institute, Program, and Year are NOT case-normalized -- typed/stored
    case is kept as-is.
    """
    institute_s = sanitize_path_component(institute)
    program_s = sanitize_path_component(program)
    year_s = sanitize_path_component(year)
    session_s = sanitize_path_component(session).lower()
    scheme_s = sanitize_path_component(scheme).upper()
    return os.path.join(base_dir, institute_s, program_s, year_s, session_s, f"{scheme_s}.db")


def ensure_scheme_db(institute, program, year, session, scheme, base_dir="."):
    """Computes this scheme's database path (see scheme_db_path()), and
    -- the first time this exact (institute, program, year, session,
    scheme) combination is selected -- creates its parent folder and its
    tables (via init_db(), which is idempotent: CREATE TABLE IF NOT
    EXISTS means calling this again on an already-populated database
    changes nothing). Returns the path either way.
    """
    path = scheme_db_path(institute, program, year, session, scheme, base_dir)
    parent = os.path.dirname(path)
    if parent:
        os.makedirs(parent, exist_ok=True)
    init_db(path)
    return path


def set_active_scheme_db(path):
    """The one place a scheme selection actually takes effect. Every
    function elsewhere in this module that reads/writes scheme-scoped
    data is called with db_path=DB_FILE (explicitly, from app.py) --
    so reassigning DB_FILE here is what makes Train, Extract, Course
    Codes, Recheck, Offline Import, and Report all transparently start
    working against the newly selected scheme's database, without any
    of those modules' own code changing or knowing a switch happened.
    """
    global DB_FILE
    DB_FILE = path


def record_scheme_declaration(institute, program, year, session, scheme, source, db_path=SEATING_DB_FILE):
    """Records that an (institute, program, year, session, scheme)
    combination's database exists, regardless of HOW it came to exist --
    via the normal paste-based path (source="paste") or via manual entry
    (source="manual"), for when no seating chart is available at all.

    This is deliberately separate from the seating_chart table itself:
    a manually-declared scheme has no actual student rows behind it, so
    it can't be discovered via list_active_schemes() (which reads
    DISTINCT scheme FROM seating_chart). This table is what lets the
    scheme picker show EVERY known scheme for a given institute/program/
    year/session, paste-detected or manually-declared, as one combined
    list, with no distinction visible downstream (see get_known_schemes()).

    Sanitized values are stored (matching the actual filename), not the
    raw typed text, so lookups are consistent regardless of how the user
    typed "2025-2026" vs "2025 2026". Safe to call repeatedly for the
    same combination -- INSERT OR IGNORE means a re-declaration is a
    no-op, not a duplicate row or an error.
    """
    institute_s = sanitize_path_component(institute)
    program_s = sanitize_path_component(program)
    year_s = sanitize_path_component(year)
    session_s = sanitize_path_component(session).lower()
    scheme_s = sanitize_path_component(scheme).upper()

    conn = sqlite3.connect(db_path)
    conn.execute("""
        CREATE TABLE IF NOT EXISTS scheme_declarations (
            institute TEXT NOT NULL,
            program TEXT NOT NULL,
            year TEXT NOT NULL,
            session TEXT NOT NULL,
            scheme TEXT NOT NULL,
            source TEXT NOT NULL,          -- 'paste' or 'manual'
            UNIQUE(institute, program, year, session, scheme)
        )
    """)
    # Migration: a scheme_declarations table created before 'institute'
    # existed -- add the column so older rows don't crash the INSERT
    # below (they'll just have an empty institute until re-declared).
    existing_cols = {row[1] for row in conn.execute("PRAGMA table_info(scheme_declarations)")}
    if "institute" not in existing_cols:
        conn.execute("ALTER TABLE scheme_declarations ADD COLUMN institute TEXT NOT NULL DEFAULT ''")
    conn.execute(
        "INSERT OR IGNORE INTO scheme_declarations (institute, program, year, session, scheme, source) "
        "VALUES (?, ?, ?, ?, ?, ?)",
        (institute_s, program_s, year_s, session_s, scheme_s, source),
    )
    conn.commit()
    conn.close()


def get_known_schemes(institute, program, year, session, db_path=SEATING_DB_FILE):
    """Every scheme letter known for this (institute, program, year,
    session) -- from EITHER path, combined, with no way to tell which
    path a given letter came from (that distinction only exists in the
    'source' column for debugging; nothing downstream reads it). This is
    the single list a scheme picker should show.
    """
    institute_s = sanitize_path_component(institute)
    program_s = sanitize_path_component(program)
    year_s = sanitize_path_component(year)
    session_s = sanitize_path_component(session).lower()

    conn = sqlite3.connect(db_path)
    try:
        rows = conn.execute(
            "SELECT DISTINCT scheme FROM scheme_declarations "
            "WHERE institute = ? AND program = ? AND year = ? AND session = ? ORDER BY scheme",
            (institute_s, program_s, year_s, session_s),
        ).fetchall()
    except sqlite3.OperationalError:
        rows = []
    conn.close()
    return [r[0] for r in rows]


def list_all_scheme_declarations(institute, program, db_path=SEATING_DB_FILE):
    """Every (year, session, scheme) combination ever declared for THIS
    (institute, program) pair specifically -- across every exam sitting,
    from EITHER the paste path or manual entry. This is the flat list
    the sidebar's single-select radio picker shows.

    Filtered to exactly one institute+program on purpose: `program` is,
    in practice, a logged-in department's own name, and a department
    should only ever see and select among schemes IT declared -- never
    another department's (even within the same institute), and never
    another institute's at all. Most recently declared first.

    Returns a list of dicts: {"institute", "program", "year", "session",
    "scheme"} (already-sanitized values, matching each one's actual
    filename).
    """
    institute_s = sanitize_path_component(institute)
    program_s = sanitize_path_component(program)

    conn = sqlite3.connect(db_path)
    try:
        rows = conn.execute(
            "SELECT institute, program, year, session, scheme FROM scheme_declarations "
            "WHERE institute = ? AND program = ? ORDER BY rowid DESC",
            (institute_s, program_s),
        ).fetchall()
    except sqlite3.OperationalError:
        rows = []
    conn.close()
    return [
        {"institute": r[0], "program": r[1], "year": r[2], "session": r[3], "scheme": r[4]} for r in rows
    ]

# If a captcha is mistyped, MSBTE's site doesn't say "wrong captcha" --
# it just re-shows a results page with zero tables on it, which looks
# identical to "this enrollment number has no result." So in extract
# mode, a zero-table result is treated as a probable wrong captcha and
# retried (fresh captcha popup) up to this many EXTRA times before it's
# finally logged for review and the batch moves on to the next enrollment.
MAX_CAPTCHA_RETRIES = 4

SEMESTER_NAMES = [
    "FIRST SEMESTER", "SECOND SEMESTER", "THIRD SEMESTER",
    "FOURTH SEMESTER", "FIFTH SEMESTER", "FINAL SEMESTER",
]

# Pairs of semesters that make up one academic year, for the history
# report's per-year block of columns (Failed Count / Average Marks /
# Total Sum of Subjects / Eligible-Non-Eligible for Next Year) -- values
# are computed from whichever semester(s) in the pair a given enrollment
# actually has data for (so a student only through Semester 1 still gets
# a First Year Failed Count from Semester 1 alone, not a blank, until
# Semester 2 lands).
YEAR_GROUPS = [
    ("First Year", ["FIRST SEMESTER", "SECOND SEMESTER"]),
    ("Second Year", ["THIRD SEMESTER", "FOURTH SEMESTER"]),
    ("Final Year", ["FIFTH SEMESTER", "FINAL SEMESTER"]),
]

# Eligibility rule for the Yearly Result report's "Eligible/Non-Eligible for Next
# Year" column: given a year's total subject count (both semesters
# combined), how many of those subjects can a student have failed and
# still be eligible? The table follows a clean pattern -- one more
# allowed failure per 3 additional subjects -- so it's implemented as
# total_subjects // 3 rather than a literal lookup table, and extends
# cleanly past 18 subjects on the same pattern:
#   subjects: 1  2  3  4  5  6  7  8  9  10 11 12 13 14 15 16 17 18
#   allowed:  0  0  1  1  1  2  2  2  3  3  3  4  4  4  5  5  5  6
def max_allowed_failed_for_eligibility(total_subjects):
    return total_subjects // 3


def compute_year_eligibility_and_remark(failed_count, total_subjects, lower_year_failed_count):
    """The shared Eligible/Non-Eligible-for-Next-Year rule, used by BOTH
    the Yearly Result report and the Yearly Eligible/Non-Eligible Student
    List, so the two reports can never disagree with each other.

    Rule 1: Eligible if failed_count <= max_allowed_failed_for_eligibility
    (total_subjects) -- i.e. within the allowed-failures table above.

    Rule 2 (applied on top of Rule 1): even where Rule 1 says Eligible,
    an enrollment with any unresolved failures in the immediately LOWER
    year (that year's own Failed Count > 0) is forced to Not Eligible for
    THIS higher year instead, with a "Lower Semester Pending" remark --
    e.g. an enrollment that's reached Third/Fourth Semester (so it has a
    Second Year row) but still has a failed subject sitting in First Year
    shouldn't show up as cleanly Eligible for Second Year.

    lower_year_failed_count: pass "" (or None) for a year with no lower
    year to check (First Year), or when that lower year has no data yet
    -- either way, Rule 2 simply doesn't apply.

    Returns (eligibility, remark) -- both "" if failed_count/total_subjects
    aren't available yet; remark is "" unless Rule 2 is what fired.
    """
    if failed_count == "" or total_subjects in ("", 0):
        return "", ""
    allowed = max_allowed_failed_for_eligibility(total_subjects)
    eligibility = "Eligible" if failed_count <= allowed else "Not Eligible"
    if lower_year_failed_count not in ("", None, 0) and lower_year_failed_count > 0:
        return "Not Eligible", "Lower Semester Pending"
    return eligibility, ""


NUMERIC_OR_DASH = re.compile(r"^-$|^\d+[#*@]?$")
GROUP_SIZE = 4  # header_info, marks, summary, instructions


# ==========================================================
# GENERIC TABLE GRID HELPERS (colspan/rowspan aware)
# Same logic as parse_msbte.py -- unchanged, just consolidated here.
# ==========================================================

def expand_table_grid(table):
    rows = table.find_all("tr")
    grid = []
    span_map = {}

    for r_idx, tr in enumerate(rows):
        if len(grid) <= r_idx:
            grid.append([])
        row = grid[r_idx]
        c_idx = 0
        cells = tr.find_all(["td", "th"])
        cell_i = 0

        while cell_i < len(cells) or (r_idx, c_idx) in span_map:
            if (r_idx, c_idx) in span_map:
                _row_extend_to(row, c_idx, span_map[(r_idx, c_idx)])
                c_idx += 1
                continue

            cell = cells[cell_i]
            text = cell.get_text(" ", strip=True)
            colspan = int(cell.get("colspan", 1) or 1)
            rowspan = int(cell.get("rowspan", 1) or 1)

            for span_c in range(colspan):
                col = c_idx + span_c
                _row_extend_to(row, col, text)
                for span_r in range(1, rowspan):
                    span_map[(r_idx + span_r, col)] = text

            c_idx += colspan
            cell_i += 1

        grid[r_idx] = row

    width = max((len(r) for r in grid), default=0)
    for row in grid:
        while len(row) < width:
            row.append("")
    return grid


def _row_extend_to(row, col, value):
    while len(row) <= col:
        row.append("")
    row[col] = value


def extract_semester_label(header_grid):
    """
    A merged cell repeats its value across every column it spans (see
    expand_table_grid), so we collapse consecutive duplicates first to
    approximate the original per-cell layout before label:value pairing.
    The leftover unpaired cell in a row is the semester name.
    """
    for row in header_grid:
        deduped = [c for i, c in enumerate(row) if i == 0 or c != row[i - 1]]
        cells = [c for c in deduped if c != ""]
        i = 0
        while i < len(cells) - 1:
            i += 2
        if i == len(cells) - 1:
            candidate = cells[i].strip().upper()
            if candidate in SEMESTER_NAMES:
                return candidate
            return cells[i].strip()  # fallback: still return whatever was found
    return None


def group_tables(tables, group_size=GROUP_SIZE):
    chunks = [tables[i:i + group_size] for i in range(0, len(tables), group_size)]
    return [c for c in chunks if len(c) == group_size]


def is_data_row(row):
    """Same heuristic as parse_msbte.py: a row is 'data' if most of its
    cells (excluding the first, which is usually a name/label) look
    numeric/dash."""
    rest = row[1:]
    if not rest:
        return False
    numeric_like = sum(1 for c in rest if NUMERIC_OR_DASH.match(c.strip()))
    return (numeric_like / len(rest)) > 0.5


# ==========================================================
# CAPTCHA + LIVE FETCH  (from the existing scraper, unchanged behavior:
# captcha is ALWAYS entered manually via the popup, every single call)
# ==========================================================

# --- Single persistent (hidden) Tk root, shared by every popup dialog in
# this file. ---
# THE BUG THIS FIXES: every dialog used to do `root = tk.Tk(); ...;
# root.mainloop()`, creating a brand-new Tk() interpreter instance each
# time. That's reliable for the FIRST dialog shown in the process, but a
# second tk.Tk() call after the first one is destroyed is unreliable in
# CPython/Tkinter -- it commonly just hangs with no window ever appearing
# (no error, no crash -- it looks exactly like "processing silently
# stopped"). That's why extract mode appeared to stop after the first
# enrollment's captcha popup, and train mode could do the same after the
# first semester's range-selector dialog if the samples spanned more than
# one semester.
# THE FIX: create exactly one hidden Tk() root for the whole process, and
# make every dialog a Toplevel() of that shared root, blocking via
# `root.grab_set(); root.wait_window()` instead of its own mainloop(). This
# is the standard, well-supported Tkinter pattern for showing any number
# of sequential modal dialogs in one process.
_APP_ROOT = None


def _get_app_root():
    global _APP_ROOT
    if _APP_ROOT is None:
        _APP_ROOT = tk.Tk()
        _APP_ROOT.withdraw()  # never shown itself -- only dialogs (Toplevels) off it are
    return _APP_ROOT


def get_captcha_from_popup(image_path):
    root = tk.Toplevel(_get_app_root())
    root.attributes("-topmost", True)
    root.title("MSBTE Captcha")
    root.resizable(False, False)

    img = Image.open(image_path)
    photo = ImageTk.PhotoImage(img)
    lbl_img = tk.Label(root, image=photo)
    lbl_img.image = photo
    lbl_img.pack(padx=10, pady=10)

    tk.Label(root, text="Enter Captcha").pack()
    captcha_var = tk.StringVar()
    entry = tk.Entry(root, textvariable=captcha_var, font=("Arial", 14))
    entry.pack(padx=10, pady=5)
    entry.focus()

    result = {"captcha": ""}

    def submit():
        result["captcha"] = captcha_var.get().strip()
        root.destroy()

    ttk.Button(root, text="Submit", command=submit).pack(pady=10)
    root.bind("<Return>", lambda e: submit())
    root.grab_set()
    root.wait_window()
    return result["captcha"]


def fetch_result_html(session, enrollment):
    """
    Returns the raw HTML text of the result page for `enrollment`, or
    None if the fetch/captcha step failed. Captcha is always solved
    manually via the popup -- no automated OCR here.
    """
    r = session.get(MSBTE_URL)
    soup = BeautifulSoup(r.text, "html.parser")

    try:
        viewstate = soup.find("input", {"name": "__VIEWSTATE"})["value"]
        eventvalidation = soup.find("input", {"name": "__EVENTVALIDATION"})["value"]
        viewstategenerator = soup.find("input", {"name": "__VIEWSTATEGENERATOR"})["value"]
        txt_captcha_cold = soup.find("input", {"name": "txtCaptchaCold"})["value"]
        txt_uri_no = soup.find("input", {"name": "txtUriNo"})["value"]
        txt_prev_uri_offset = soup.find("input", {"name": "txtPrevUriOffSet"})["value"]
        captcha_src = soup.find("img", {"id": "imgCaptcha"})["src"]
    except (TypeError, KeyError) as e:
        print(f"  Could not read the MSBTE form (page structure may have changed): {e}")
        return None

    captcha_url = "https://result.msbte.ac.in/pcwebBTRes/" + captcha_src.replace("../", "")
    img_resp = session.get(captcha_url)
    with open(CAPTCHA_IMG, "wb") as f:
        f.write(img_resp.content)

    captcha = get_captcha_from_popup(CAPTCHA_IMG)

    if os.path.exists(CAPTCHA_IMG):
        os.remove(CAPTCHA_IMG)

    if not captcha:
        print("  Captcha entry cancelled/empty, skipping.")
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

    r2 = session.post(MSBTE_URL, data=payload)
    return r2.text


def fetch_result_html_with_retry(session, enrollment, max_retries=MAX_CAPTCHA_RETRIES):
    """Like fetch_result_html(), but if the page comes back with ZERO
    result tables -- almost always a mistyped captcha rather than a
    genuinely bad enrollment number -- it re-prompts for a fresh captcha
    and tries again for the SAME enrollment, up to `max_retries` extra
    times.

    Returns (html, attempts):
      html     -- the last HTML fetched, or None if captcha entry was
                  cancelled/empty (user gave up on the popup).
      attempts -- how many fetch attempts were made (for logging).

    Note this can't fully tell "wrong captcha" apart from "this
    enrollment truly has no result" -- both look like zero tables on
    the page. Capping retries at MAX_CAPTCHA_RETRIES keeps a genuinely
    bad enrollment number from looping forever while still giving a
    mistyped captcha several extra chances.
    """
    attempt = 0
    while True:
        attempt += 1
        html = fetch_result_html(session, enrollment)
        if not html:
            # Captcha popup cancelled/empty -- nothing to retry.
            return None, attempt

        soup = BeautifulSoup(html, "html.parser")
        if soup.find_all("table"):
            return html, attempt

        if attempt > max_retries:
            return html, attempt

        print(f"  No result tables found for {enrollment} -- likely a wrong captcha entry. "
              f"Retrying ({attempt}/{max_retries} retries used) ...")


# ==========================================================
# TRAIN MODE
# ==========================================================

def ask_enrollment_numbers():
    root = tk.Toplevel(_get_app_root())
    root.title("MSBTE Tool - Train Mode: Enter Sample Enrollment Numbers")
    root.attributes("-topmost", True)

    tk.Label(
        root,
        text=("Enter up to 6 sample enrollment numbers (any student, any order).\n"
              "One enrollment can cover several semesters at once -- that's fine,\n"
              "overlapping semesters get cross-checked automatically. Leave blank to skip."),
        justify="left",
    ).grid(row=0, column=0, columnspan=2, padx=10, pady=(10, 5), sticky="w")

    entries = []
    for i in range(6):
        tk.Label(root, text=f"Enrollment #{i + 1}:").grid(row=i + 1, column=0, padx=10, pady=4, sticky="e")
        var = tk.StringVar()
        tk.Entry(root, textvariable=var, width=25).grid(row=i + 1, column=1, padx=10, pady=4, sticky="w")
        entries.append(var)

    result = {"values": []}

    def submit():
        result["values"] = [e.get().strip() for e in entries if e.get().strip()]
        root.destroy()

    # Vertical button column on the right side, spanning the height of the entry rows
    btn_frame = tk.Frame(root)
    btn_frame.grid(row=1, column=2, rowspan=6, padx=(15, 10), pady=4, sticky="ns")
    ttk.Button(btn_frame, text="Fetch\nThese", command=submit).pack(fill="both", expand=True)

    root.grab_set()
    root.wait_window()
    return result["values"]


def cross_check_samples(samples):
    """
    samples: {semester_label: [(enrollment, chunk_of_4_tables), ...]}
    Returns a list of human-readable warning strings for any semester
    label seen from more than one enrollment where the table shapes
    (num_rows x num_cols per table position) don't match.
    """
    warnings = []
    for label, entries in samples.items():
        if len(entries) < 2:
            continue
        base_enr, base_chunk = entries[0]
        base_shapes = [_table_shape(t) for t in base_chunk]
        for enr, chunk in entries[1:]:
            shapes = [_table_shape(t) for t in chunk]
            if shapes != base_shapes:
                warnings.append(
                    f"{label}: enrollment {base_enr} has shape {base_shapes}, "
                    f"but enrollment {enr} has shape {shapes}. "
                    f"These should match -- investigate before trusting this mapping."
                )
    return warnings


def _table_shape(table):
    grid = expand_table_grid(table)
    rows = len(grid)
    cols = len(grid[0]) if grid else 0
    return (rows, cols)


class SelectableGrid:
    """
    An Excel-like grid of cells inside a tk container: click a cell,
    drag to mark a rectangle. Hold CTRL while dragging to ADD another
    rectangle to the current selection (like Excel's Ctrl+click-drag
    for non-contiguous ranges) -- needed for things like Maximum Marks,
    where the MAX columns alternate with OBT columns and aren't one
    contiguous block. A plain (non-Ctrl) drag clears previous
    rectangles and starts a fresh selection.

    Column width and font size shrink automatically as a table gets
    wider so the ENTIRE table is always visible without horizontal
    scrolling -- previously, reaching hidden right-hand columns meant
    scrolling right, which required holding CTRL to avoid losing
    whatever had already been selected.
    """

    TARGET_TABLE_WIDTH_PX = 1000  # conservative: fits alongside the 220px side panel in the 1400px window
    CTRL_MASK = 0x0004

    @staticmethod
    def _pick_cell_size(num_cols, available_width=TARGET_TABLE_WIDTH_PX):
        """
        Try progressively smaller font sizes / column widths and measure
        the ACTUAL rendered pixel width (via tkinter.font, not a guess)
        until the whole row of columns fits inside available_width.
        Guarantees every column is on-screen -- no horizontal scrolling.
        """
        num_cols = max(num_cols, 1)
        border_padding_per_cell = 6  # ~ relief/bd + internal padx of each Label
        for font_size in (9, 8, 7, 6, 5, 4):
            f = tkfont.Font(family="Arial", size=font_size)
            for cell_width in range(13, 2, -1):
                row_header_w = max(3, min(5, cell_width))
                header_px = f.measure("0" * row_header_w) + border_padding_per_cell
                cell_px = f.measure("0" * cell_width) + border_padding_per_cell
                total_px = header_px + cell_px * num_cols
                if total_px <= available_width:
                    return cell_width, font_size
        return 3, 4

    def __init__(self, parent, grid_data, title, position=None, on_change=None, available_width=None):
        self.grid_data = grid_data
        self.num_rows = len(grid_data)
        self.num_cols = max((len(r) for r in grid_data), default=0)
        self.cells = {}
        self.anchor = None
        self.preview = None       # in-progress rect being dragged: (r0, c0, r1, c1)
        self.selections = []      # committed rects: [(row_start, row_end, col_start, col_end), ...]
        self.position = position  # position_in_group (0,1,2,3...) this grid represents
        self.on_change = on_change  # called with `self` whenever a rectangle is committed (on release)

        cell_width, font_size = self._pick_cell_size(
            self.num_cols, available_width if available_width is not None else self.TARGET_TABLE_WIDTH_PX)
        row_label_width = max(3, min(5, cell_width))

        self.container = tk.LabelFrame(parent, text=title, font=("Arial", 10, "bold"))
        self.container.pack(fill="x", padx=10, pady=8)

        grid_frame = tk.Frame(self.container)
        grid_frame.pack(side="top", anchor="w", padx=4, pady=4)

        tk.Label(grid_frame, text="", width=row_label_width, relief="ridge", bg="#dddddd").grid(row=0, column=0)
        for c in range(self.num_cols):
            tk.Label(grid_frame, text=f"c{c}", width=cell_width, relief="ridge",
                     bg="#dddddd", font=("Arial", max(font_size - 1, 6), "bold")).grid(row=0, column=c + 1)

        for r in range(self.num_rows):
            tk.Label(grid_frame, text=f"r{r}", width=row_label_width, relief="ridge",
                     bg="#dddddd", font=("Arial", max(font_size - 1, 6), "bold")).grid(row=r + 1, column=0)
            row_vals = grid_data[r]
            for c in range(self.num_cols):
                text = row_vals[c] if c < len(row_vals) else ""
                lbl = tk.Label(grid_frame, text=text[:cell_width + 2], relief="solid", bd=1,
                                bg="white", font=("Arial", font_size), anchor="w")
                lbl.grid(row=r + 1, column=c + 1, sticky="nsew")
                lbl.bind("<Button-1>", lambda e, rr=r, cc=c: self._on_down(e, rr, cc))
                lbl.bind("<Control-Button-1>", lambda e, rr=r, cc=c: self._on_down(e, rr, cc))
                lbl.bind("<B1-Motion>", self._on_drag)
                lbl.bind("<Control-B1-Motion>", self._on_drag)
                lbl.bind("<ButtonRelease-1>", self._on_release)
                self.cells[(r, c)] = lbl

        tk.Label(self.container,
                 text=f"({self.num_cols} columns -- auto-sized to fit on screen, no scrolling needed). "
                      f"Hold CTRL while dragging to add another range (like Excel).",
                 font=("Arial", 8, "italic"), fg="#666666").pack(anchor="w", padx=4, pady=(0, 4))

    def _on_down(self, event, r, c):
        additive = bool(event.state & self.CTRL_MASK)
        if not additive:
            self.selections = []  # plain click/drag starts a fresh selection
        self.anchor = (r, c)
        self.preview = (r, c, r, c)
        self._redraw()

    def _on_drag(self, event):
        widget = event.widget.winfo_containing(event.x_root, event.y_root)
        for (r, c), w in self.cells.items():
            if w is widget:
                self.preview = (self.anchor[0], self.anchor[1], r, c)
                self._redraw()
                break

    def _on_release(self, event):
        if self.preview is not None:
            r0, c0, r1, c1 = self.preview
            r_start, r_end = sorted((r0, r1))
            c_start, c_end = sorted((c0, c1))
            self.selections.append((r_start, r_end, c_start, c_end))
            self.preview = None
            self._redraw()
        if self.on_change:
            self.on_change(self)

    def _redraw(self):
        committed_cells = set()
        for (r0, r1, c0, c1) in self.selections:
            for r in range(r0, r1 + 1):
                for c in range(c0, c1 + 1):
                    committed_cells.add((r, c))

        preview_cells = set()
        if self.preview is not None:
            r0, c0, r1, c1 = self.preview
            r_start, r_end = sorted((r0, r1))
            c_start, c_end = sorted((c0, c1))
            for r in range(r_start, r_end + 1):
                for c in range(c_start, c_end + 1):
                    preview_cells.add((r, c))

        for (r, c), lbl in self.cells.items():
            if (r, c) in preview_cells:
                lbl.configure(bg="#ffcc66")   # amber while actively dragging
            elif (r, c) in committed_cells:
                lbl.configure(bg="#a8d8ff")   # blue for committed rectangles
            else:
                lbl.configure(bg="white")

    def get_selections(self):
        return list(self.selections)  # possibly several rectangles

    def clear_selections(self):
        self.selections = []
        self.preview = None
        self._redraw()


GROUPS = [
    ("year", "Year"),
    ("program", "Program"),
    ("name", "Name"),
    ("enrollment_number", "Enrollment Number"),
    ("seat_number", "Seat Number"),
    ("semester", "Semester"),
    ("subjects", "Subjects"),
    ("maximum_marks", "Maximum Marks"),
    ("obtained_marks", "Obtained Marks"),
    ("thprsla", "THPRSLA"),
    ("fasa", "FASA"),
    ("total_marks", "Total Marks"),
    ("obtained_total_marks", "Obtained Total Marks"),
    ("percentage", "Percentage"),
    ("result", "Result"),
]

# These 5 groups are the separate pieces of a student's identity line
# (previously everything got lumped into just "name_seat"). Order here is
# display order, left to right, BEFORE the subject columns. "program" was
# added at the front (e.g. "Diploma in Computer Engineering") since it's
# a per-student identity field selected first in train mode, same as the
# other identity groups -- not a semester-constant heading, since MSBTE
# groups tables per-student and program text sits with the rest of the
# identity line on each student's own page.
#
# "year" (the exam session, e.g. "SUMMER-2026") is trained/extracted the
# exact same per-student way as these -- see GROUPS above -- but is
# deliberately NOT in this list: it's constant across every student in a
# semester's batch, so it'd be a pointless repeated column if it were
# shown per-student like Program/Name are. Instead it's only read back via
# get_semester_identity_text(), for the report heading block (Academic
# Year / Exam Summer-Winter -- see parse_exam_session()).
IDENTITY_GROUPS = ["program", "name", "enrollment_number", "seat_number", "semester"]
IDENTITY_GROUP_LABELS = {
    "program": "Program",
    "name": "Name",
    "enrollment_number": "Enrollment Number",
    "seat_number": "Seat Number",
    "semester": "Semester",
}

# These 4 groups are the separate pieces of a student's summary line
# (previously everything got lumped into just "result", which is why a
# 4-column summary rendered as if only the last column mattered -- each
# now gets its own labeled block in the report). Order here is display
# order, left to right, after the subject columns.
SUMMARY_GROUPS = ["total_marks", "obtained_total_marks", "percentage", "result"]
SUMMARY_GROUP_LABELS = {
    "total_marks": "Total Marks",
    "obtained_total_marks": "Obtained Total",
    "percentage": "Percentage",
    "result": "Result",
}

# Groups whose row range should auto-extend to however many subject rows a
# given student actually has (subject count varies per student/semester).
# The other groups are single static rows/blocks (identity fields, header
# labels, summary line) and use exactly the row range trained, no extension.
DYNAMIC_GROUPS = {"subjects", "maximum_marks", "obtained_marks"}

# subjects/THPRSLA/FASA/maximum_marks describe the fixed structure of a
# semester's mark sheet -- same for every student -- so they're headings.
# obtained_marks, the identity groups, and the summary groups are the
# actual per-student data.
HEADING_GROUPS = {"subjects", "thprsla", "fasa", "maximum_marks"}


# ==========================================================
# SUBJECT-WISE TRAINING v2 (scheme-agnostic, nested template tree)
# ==========================================================
# v1 (component defined independently per subject) worked but meant
# re-defining "FA-TH", "SA-TH", etc. by hand for every single subject.
# v2 splits that into two things trained separately:
#
#   1. A TEMPLATE: one shared nested tree of component labels, defined
#      ONCE for the whole semester -- e.g. Level 1: TH / PR / SLA,
#      Level 2 under TH: FA / SA / Total, Level 3 under FA: "Max marks"
#      (up to 4 levels). This tree also becomes the multi-row report
#      header later (Level 1/2/3 labels stack as header rows), which is
#      exactly the shape MSBTE's own mark sheets use.
#
#   2. Per-subject CHECKBOX overrides: since not every subject has every
#      branch (a Practical-only subject has no TH branch), each subject
#      just has some nodes switched off rather than a whole separate
#      component set defined from scratch. Off by default cascades to
#      every descendant. On by default.
#
# The actual mark values (Max/Obtained) are trained per LEAF per subject
# (Step 6) -- reusing the same drag-select-then-Add group mechanism as
# the flat range selector, just scoped to one leaf at a time.
#
# Extraction (extract_subjectwise_from_chunk) still just reads back
# exactly the cells that were trained, for whichever leaves are enabled
# for a given subject -- no scheme branching anywhere.

MAX_TEMPLATE_LEVELS = 4


def save_component_template_settings(semester_label, max_levels, db_path=DB_FILE):
    conn = sqlite3.connect(db_path)
    conn.execute(
        "INSERT INTO semester_template_settings (semester_label, max_levels) VALUES (?, ?) "
        "ON CONFLICT(semester_label) DO UPDATE SET max_levels=excluded.max_levels",
        (semester_label, max_levels),
    )
    conn.commit()
    conn.close()


def load_component_template_settings(semester_label, db_path=DB_FILE):
    conn = sqlite3.connect(db_path)
    row = conn.execute(
        "SELECT max_levels FROM semester_template_settings WHERE semester_label = ?",
        (semester_label,),
    ).fetchone()
    conn.close()
    return row[0] if row else None


def save_subjects_to_db(semester_label, subjects, db_path=DB_FILE):
    """subjects: list of dicts {index, name, position, abs_row, abs_col} --
    each just ONE cell (the subject's name), selected sequentially in
    Step 1. Retrain-safe: replaces this semester's subject list wholesale."""
    conn = sqlite3.connect(db_path)
    conn.execute("DELETE FROM subjects WHERE semester_label = ?", (semester_label,))
    for s in subjects:
        conn.execute(
            "INSERT INTO subjects (semester_label, subject_index, subject_name, position, abs_row, abs_col) "
            "VALUES (?,?,?,?,?,?)",
            (semester_label, s["index"], s["name"], s["position"], s["abs_row"], s["abs_col"]),
        )
    conn.commit()
    conn.close()


def load_subjects(semester_label, db_path=DB_FILE):
    conn = sqlite3.connect(db_path)
    conn.row_factory = sqlite3.Row
    rows = conn.execute(
        "SELECT * FROM subjects WHERE semester_label = ? ORDER BY subject_index", (semester_label,)
    ).fetchall()
    conn.close()
    return [dict(r) for r in rows]


def save_component_template_to_db(semester_label, nodes, db_path=DB_FILE):
    """nodes: list of dicts {node_id, parent_id, level, label} forming the
    shared tree (parent_id is None for level-1 nodes). Retrain-safe:
    replaces this semester's whole template."""
    conn = sqlite3.connect(db_path)
    conn.execute("DELETE FROM component_template WHERE semester_label = ?", (semester_label,))
    for n in nodes:
        conn.execute(
            "INSERT INTO component_template (semester_label, node_id, parent_id, level, label) "
            "VALUES (?,?,?,?,?)",
            (semester_label, n["node_id"], n["parent_id"], n["level"], n["label"]),
        )
    conn.commit()
    conn.close()


def load_component_template(semester_label, db_path=DB_FILE):
    """Returns a flat list of node dicts. Use build_template_children_map()
    to walk it as a tree."""
    conn = sqlite3.connect(db_path)
    conn.row_factory = sqlite3.Row
    rows = conn.execute(
        "SELECT * FROM component_template WHERE semester_label = ? ORDER BY level, node_id",
        (semester_label,),
    ).fetchall()
    conn.close()
    return [dict(r) for r in rows]


def build_template_children_map(nodes):
    """parent_id -> [child node dicts], with None as the root key (level-1
    nodes)."""
    children = {}
    for n in nodes:
        children.setdefault(n["parent_id"], []).append(n)
    return children


def leaf_nodes(nodes):
    """Nodes with no children -- these are what Step 6 collects Max/
    Obtained cells for."""
    parent_ids = {n["parent_id"] for n in nodes if n["parent_id"] is not None}
    return [n for n in nodes if n["node_id"] not in parent_ids]


def node_path_label(node_id, nodes_by_id, sep=" \u2192 "):
    parts = []
    n = nodes_by_id.get(node_id)
    while n is not None:
        parts.append(n["label"])
        n = nodes_by_id.get(n["parent_id"]) if n["parent_id"] is not None else None
    return sep.join(reversed(parts))


def save_subject_node_disabled(semester_label, disabled_pairs, db_path=DB_FILE):
    """disabled_pairs: list of (subject_index, node_id) that are unchecked
    for that subject. Replaces this semester's whole disabled set."""
    conn = sqlite3.connect(db_path)
    conn.execute("DELETE FROM subject_node_disabled WHERE semester_label = ?", (semester_label,))
    for subject_index, node_id in disabled_pairs:
        conn.execute(
            "INSERT OR IGNORE INTO subject_node_disabled (semester_label, subject_index, node_id) "
            "VALUES (?,?,?)",
            (semester_label, subject_index, node_id),
        )
    conn.commit()
    conn.close()


def load_subject_node_disabled(semester_label, db_path=DB_FILE):
    """Returns a set of (subject_index, node_id) pairs that are explicitly
    unchecked."""
    conn = sqlite3.connect(db_path)
    rows = conn.execute(
        "SELECT subject_index, node_id FROM subject_node_disabled WHERE semester_label = ?",
        (semester_label,),
    ).fetchall()
    conn.close()
    return {(r[0], r[1]) for r in rows}


def node_enabled_for_subject(node_id, subject_index, nodes_by_id, disabled_set):
    """A node is enabled for a subject only if it, and every ancestor of
    it, is NOT in the disabled set -- unchecking a branch cascades down."""
    n = nodes_by_id.get(node_id)
    while n is not None:
        if (subject_index, n["node_id"]) in disabled_set:
            return False
        n = nodes_by_id.get(n["parent_id"]) if n["parent_id"] is not None else None
    return True


def save_subject_node_values_to_db(semester_label, values, db_path=DB_FILE):
    """values: list of dicts {subject_index, node_id, role, position,
    abs_row, abs_col} -- the trained Max/Obtained cell for one leaf, one
    subject. Upserts (safe to re-train a single leaf without wiping the
    rest)."""
    conn = sqlite3.connect(db_path)
    for v in values:
        conn.execute(
            "INSERT INTO subject_node_values "
            "(semester_label, subject_index, node_id, role, position, abs_row, abs_col) "
            "VALUES (?,?,?,?,?,?,?) "
            "ON CONFLICT(semester_label, subject_index, node_id, role) "
            "DO UPDATE SET position=excluded.position, abs_row=excluded.abs_row, abs_col=excluded.abs_col",
            (semester_label, v["subject_index"], v["node_id"], v["role"],
             v["position"], v["abs_row"], v["abs_col"]),
        )
    conn.commit()
    conn.close()


def load_subject_node_values(semester_label, db_path=DB_FILE):
    conn = sqlite3.connect(db_path)
    conn.row_factory = sqlite3.Row
    rows = conn.execute(
        "SELECT * FROM subject_node_values WHERE semester_label = ?", (semester_label,)
    ).fetchall()
    conn.close()
    return [dict(r) for r in rows]


def list_subjectwise_semesters(db_path=DB_FILE):
    conn = sqlite3.connect(db_path)
    rows = conn.execute("SELECT DISTINCT semester_label FROM subjects").fetchall()
    conn.close()
    return [r[0] for r in rows]


# ==========================================================
# ONE-DRAG TRAINING ENGINE (v3)
# ==========================================================
# Replaces the old per-subject / per-leaf click-and-Add trainer (Steps
# 1-6) with exactly 4-5 drags, done once, in order:
#   Whole Table -> Subjects -> Level 1 -> Level 2 -> ... -> Max+Obtained
#
# Orientation (horizontal = K-scheme-style columns-are-components,
# vertical = I-scheme-style variable-height row-blocks-are-subjects) is
# asked explicitly once per semester in app.py (a Common/Varies choice
# shown right after Subjects is confirmed) and then applies to every
# Level drag for that semester. classify_drag_shape() below is kept as a
# general-purpose row-vs-column classifier (still handy for sanity-
# checking a drag) but the UI no longer uses it to infer orientation.
#
# Whichever orientation is used, the OUTPUT is identical: rows in
# subjects/component_template (and, for horizontal, subject_node_values;
# for vertical, subjectwise_vertical_roles instead, since row position
# isn't fixed per student there). Every report function already reads
# only from subjects/component_template/subjectwise_student_records, so
# none of that code needs to know or care which orientation trained it.

def classify_drag_shape(row_start, row_end, col_start, col_end):
    """"row" (a shared header row -- horizontal/K-scheme-style), "column"
    (a per-row label column -- vertical/I-scheme-style), or "ambiguous"
    (a single cell, or a roughly square block) -- caller should ask the
    user explicitly only in the ambiguous case."""
    height = row_end - row_start + 1
    width = col_end - col_start + 1
    if height == 1 and width == 1:
        return "ambiguous"
    if width > height:
        return "row"
    if height > width:
        return "column"
    return "ambiguous"


def _cell(grid, row, col):
    if row < 0 or row >= len(grid):
        return ""
    r = grid[row]
    return r[col].strip() if 0 <= col < len(r) else ""


def derive_subjects_from_drag(grid, row_start, row_end, col):
    """One column, many rows (a plain click-drag straight down the
    Subject Name column) -> one subject per run of consecutive identical
    non-blank text. Blank cells (gap/spacer rows) are just skipped, not
    treated as a subject boundary by themselves -- a new subject starts
    only when the text actually changes. Naturally handles both a
    horizontal sheet (one row per subject) and a vertical one (a
    merged/rowspan title cell repeats its text across every row it
    covers -- see expand_table_grid -- so a whole multi-row subject block
    collapses into one entry with row_start/row_end spanning it)."""
    subjects = []
    current = None
    for r in range(row_start, row_end + 1):
        text = _cell(grid, r, col)
        if not text:
            continue
        if current is None or text != current["subject_name"]:
            current = {"subject_index": len(subjects) + 1, "subject_name": text,
                       "row_start": r, "row_end": r}
            subjects.append(current)
        else:
            current["row_end"] = r
    return subjects


def group_consecutive_labels(grid, row, col_start, col_end):
    """[(label, c0, c1), ...] for runs of consecutive equal non-blank text
    in `row`, restricted to [col_start, col_end]. A blank run is simply
    skipped -- not returned as its own group -- so a spacer column
    between header blocks doesn't produce a bogus node."""
    groups = []
    c = col_start
    while c <= col_end:
        text = _cell(grid, row, c)
        if not text:
            c += 1
            continue
        c0 = c
        while c + 1 <= col_end and _cell(grid, row, c + 1) == text:
            c += 1
        groups.append((text, c0, c))
        c += 1
    return groups


def build_horizontal_template(grid, level_rows, col_start, col_end):
    """level_rows: [row_for_level_1, row_for_level_2, ...], each a single
    header-row drag. Parent/child nesting falls out automatically: each
    level's label-groups are only searched for WITHIN its parent's own
    column range, so a level-2 label can never accidentally attach to the
    wrong level-1 parent. Returns (nodes, leaf_col_ranges) where
    leaf_col_ranges = {node_id: (col_start, col_end)} for the deepest
    level only -- what the Max+Obtained drag slices up next."""
    nodes = []
    next_id = [1]
    frontier = [{"node_id": None, "col_start": col_start, "col_end": col_end}]
    for level_idx, row in enumerate(level_rows, start=1):
        new_frontier = []
        for parent in frontier:
            for label, c0, c1 in group_consecutive_labels(grid, row, parent["col_start"], parent["col_end"]):
                nid = next_id[0]
                next_id[0] += 1
                nodes.append({"node_id": nid, "parent_id": parent["node_id"], "level": level_idx,
                              "label": label})
                new_frontier.append({"node_id": nid, "col_start": c0, "col_end": c1})
        frontier = new_frontier
    leaf_col_ranges = {g["node_id"]: (g["col_start"], g["col_end"]) for g in frontier}
    return nodes, leaf_col_ranges


def build_vertical_template(grid, level_cols, row_start, row_end, subjects=None):
    """level_cols: [col_for_level_1, col_for_level_2, ...], each a single
    column drag spanning every subject's rows. Reads every row's
    value-path (e.g. ("TH", "ESE")) and creates one leaf per DISTINCT
    path actually seen -- so "TH">"ESE" and "PR">"ESE" become two
    different components, matching how they're genuinely different marks
    on the real sheet.

    A blank level-column cell is forward-filled from the last non-blank
    value seen in THAT column -- MSBTE sheets often merge/rowspan the
    Level 1 (TH/PR) cell down across its ESE/PA sub-rows, but the merge
    doesn't always survive table parsing, leaving the second sub-row's
    cell blank even though it's clearly still part of the same TH/PR
    group. The fill resets at the start of each subject (via `subjects`,
    if given) so a genuinely blank/spacer row at a subject boundary never
    bleeds a value in from the previous subject."""
    nodes = []
    next_id = [1]
    node_by_path = {}
    subject_start_rows = {s["row_start"] for s in subjects} if subjects else set()
    last_values = [None] * len(level_cols)
    for r in range(row_start, row_end + 1):
        if r in subject_start_rows:
            last_values = [None] * len(level_cols)
        raw = [_cell(grid, r, c) for c in level_cols]
        values = []
        for i, v in enumerate(raw):
            if v:
                last_values[i] = v
                values.append(v)
            else:
                values.append(last_values[i])
        if not all(values):
            continue
        path = tuple(values)
        for depth in range(1, len(path) + 1):
            sub_path = path[:depth]
            if sub_path in node_by_path:
                continue
            parent_path = sub_path[:-1]
            parent_id = node_by_path[parent_path]["node_id"] if parent_path else None
            nid = next_id[0]
            next_id[0] += 1
            node = {"node_id": nid, "parent_id": parent_id, "level": depth, "label": sub_path[-1]}
            nodes.append(node)
            node_by_path[sub_path] = node
    return nodes


def find_max_obt_columns(grid, row_start, row_end, col_start, col_end):
    """Scans the given window for header-ish cells whose text starts with
    MAX / OBT(AINED) (case-insensitive) -- this is what lets ONE
    Max+Obtained drag work even when a Min Marks column sits between them
    (as in the I-scheme sheet's MAX/MIN/OBT columns): the column in
    between just never matches either pattern. Returns (max_col, obt_col),
    either of which may be None if no matching header text was found in
    that window -- caller falls back to the drag's own first/last column."""
    max_col = obt_col = None
    for r in range(row_start, row_end + 1):
        for c in range(col_start, col_end + 1):
            text = _cell(grid, r, c).upper()
            if not text:
                continue
            if max_col is None and text.startswith("MAX"):
                max_col = c
            elif obt_col is None and (text.startswith("OBT") or text.startswith("OBS")):
                obt_col = c
    return max_col, obt_col


def save_vertical_roles(semester_label, roles, db_path=DB_FILE):
    conn = sqlite3.connect(db_path)
    conn.execute(
        "INSERT INTO subjectwise_vertical_roles "
        "(semester_label, position, row_start, row_end, col_start, col_end, "
        "title_col, level_cols, max_col, obt_col) VALUES (?,?,?,?,?,?,?,?,?,?) "
        "ON CONFLICT(semester_label) DO UPDATE SET "
        "position=excluded.position, row_start=excluded.row_start, row_end=excluded.row_end, "
        "col_start=excluded.col_start, col_end=excluded.col_end, title_col=excluded.title_col, "
        "level_cols=excluded.level_cols, max_col=excluded.max_col, obt_col=excluded.obt_col",
        (semester_label, roles["position"], roles["row_start"], roles["row_end"],
         roles["col_start"], roles["col_end"], roles["title_col"], json.dumps(roles["level_cols"]),
         roles["max_col"], roles["obt_col"]),
    )
    conn.commit()
    conn.close()


def load_vertical_roles(semester_label, db_path=DB_FILE):
    conn = sqlite3.connect(db_path)
    conn.row_factory = sqlite3.Row
    row = conn.execute(
        "SELECT * FROM subjectwise_vertical_roles WHERE semester_label = ?", (semester_label,)
    ).fetchone()
    conn.close()
    if row is None:
        return None
    d = dict(row)
    d["level_cols"] = json.loads(d["level_cols"])
    return d


def is_vertical_semester(semester_label, db_path=DB_FILE):
    return load_vertical_roles(semester_label, db_path) is not None


def finalize_subjectwise_training_horizontal(semester_label, grid, position,
                                              subjects_drag, level_drags, values_drag, db_path=DB_FILE):
    """Each *_drag is its own {"row_start","row_end","col_start","col_end"}
    rectangle, taken exactly as the user dragged it -- Subjects (a column,
    data rows only, NOT the header rows), one per Level (each a header
    row), and Max+Obtained (the whole marks body: every subject row x
    every leaf's column span). Deletes any previous VERTICAL-mode
    training for this semester, since a re-train can switch orientation."""
    subjects = derive_subjects_from_drag(
        grid, subjects_drag["row_start"], subjects_drag["row_end"], subjects_drag["col_start"]
    )
    if not subjects:
        raise ValueError("No subjects found in the dragged Subjects column -- drag straight down "
                          "the column that has each subject's name (data rows only, not the header).")

    level_rows = [d["row_start"] for d in level_drags]
    col_start = level_drags[0]["col_start"]
    col_end = level_drags[0]["col_end"]
    nodes, leaf_col_ranges = build_horizontal_template(grid, level_rows, col_start, col_end)
    if not leaf_col_ranges:
        raise ValueError("No header labels found in the Level drag(s) -- make sure each Level drag "
                          "covers the row with that level's text (e.g. THEORY / PRACTICALS / SLA).")

    save_subjects_to_db(semester_label, [
        {"index": s["subject_index"], "name": s["subject_name"], "position": position,
         "abs_row": s["row_start"], "abs_col": subjects_drag["col_start"]}
        for s in subjects
    ], db_path)
    save_component_template_to_db(semester_label, nodes, db_path)
    save_component_template_settings(semester_label, len(level_rows), db_path)
    save_subject_node_disabled(semester_label, [], db_path)  # not used by this engine

    header_scan_start = min(level_rows)

    node_values = []
    for node_id, (c0, c1) in leaf_col_ranges.items():
        max_col, obt_col = find_max_obt_columns(grid, header_scan_start, values_drag["row_start"] - 1, c0, c1)
        if max_col is None:
            max_col = c0
        if obt_col is None:
            obt_col = c1
        for s in subjects:
            node_values.append({"subject_index": s["subject_index"], "node_id": node_id, "role": "max",
                                 "position": position, "abs_row": s["row_start"], "abs_col": max_col})
            node_values.append({"subject_index": s["subject_index"], "node_id": node_id, "role": "obtained",
                                 "position": position, "abs_row": s["row_start"], "abs_col": obt_col})
    save_subject_node_values_to_db(semester_label, node_values, db_path)

    # Clear any previous VERTICAL training for this semester -- a retrain
    # can switch orientation, and a stale vertical_roles row would make
    # is_vertical_semester() wrongly still route extraction that way.
    conn = sqlite3.connect(db_path)
    conn.execute("DELETE FROM subjectwise_vertical_roles WHERE semester_label = ?", (semester_label,))
    conn.commit()
    conn.close()

    return {"subjects": subjects, "nodes": nodes}


def finalize_subjectwise_training_vertical(semester_label, grid, position,
                                            subjects_drag, level_drags, values_drag, db_path=DB_FILE):
    """Same drag-rectangle inputs as the horizontal version above, but
    each Level drag is a COLUMN (one per level, spanning every subject's
    rows) instead of a header row, since a vertical layout's level values
    vary per ROW within each subject's block rather than living in a
    shared header row. Trains subjects/component_template exactly like
    horizontal (so reports don't care), but marks/max-obt positions go
    into subjectwise_vertical_roles instead of subject_node_values, since
    row position isn't fixed across students here -- see
    extract_subjectwise_vertical_from_chunk()."""
    subjects = derive_subjects_from_drag(
        grid, subjects_drag["row_start"], subjects_drag["row_end"], subjects_drag["col_start"]
    )
    if not subjects:
        raise ValueError("No subjects found in the dragged Subjects column -- drag straight down "
                          "the column that has each subject's name.")

    whole_row_start = subjects_drag["row_start"]
    whole_row_end = subjects_drag["row_end"]
    level_cols = [d["col_start"] for d in level_drags]
    nodes = build_vertical_template(grid, level_cols, whole_row_start, whole_row_end, subjects=subjects)
    if not nodes:
        raise ValueError("No component rows found across the Level drag(s) -- make sure each Level "
                          "drag covers the column with that level's per-row text (e.g. TH / PR), "
                          "spanning the same rows as the Subjects drag.")

    save_subjects_to_db(semester_label, [
        {"index": s["subject_index"], "name": s["subject_name"], "position": position,
         "abs_row": s["row_start"], "abs_col": subjects_drag["col_start"]}
        for s in subjects
    ], db_path)
    save_component_template_to_db(semester_label, nodes, db_path)
    save_component_template_settings(semester_label, len(level_cols), db_path)
    save_subject_node_disabled(semester_label, [], db_path)  # not used by this engine

    # Clear any previous HORIZONTAL training for this semester (see the
    # matching cleanup at the end of the horizontal finalizer).
    conn = sqlite3.connect(db_path)
    conn.execute("DELETE FROM subject_node_values WHERE semester_label = ?", (semester_label,))
    conn.commit()
    conn.close()

    max_col, obt_col = find_max_obt_columns(
        grid, max(whole_row_start - 3, 0), values_drag["row_start"] - 1,
        values_drag["col_start"], values_drag["col_end"]
    )
    if max_col is None:
        max_col = values_drag["col_start"]
    if obt_col is None:
        obt_col = values_drag["col_end"]

    save_vertical_roles(semester_label, {
        "position": position, "row_start": whole_row_start, "row_end": whole_row_end,
        "col_start": subjects_drag["col_start"], "col_end": subjects_drag["col_start"],
        "title_col": subjects_drag["col_start"], "level_cols": level_cols,
        "max_col": max_col, "obt_col": obt_col,
    }, db_path)
    return {"subjects": subjects, "nodes": nodes}


def extract_subjectwise_vertical_from_chunk(chunk, semester_label, enrollment, db_path=DB_FILE):
    """VERTICAL-mode counterpart to extract_subjectwise_from_chunk(). Row
    position varies per student here, so instead of replaying fixed
    (abs_row, abs_col) positions, this re-walks THIS student's actual
    rows using the trained COLUMN roles (title/level/max/obt), matching
    subjects by name and leaf components by their trained label-path --
    exactly the technique extract_i_scheme_subjects() uses, just writing
    into subjectwise_student_records so every report function downstream
    stays scheme/orientation-agnostic."""
    roles = load_vertical_roles(semester_label, db_path)
    if roles is None:
        return [], []
    if roles["position"] >= len(chunk):
        return [], [{"enrollment": enrollment, "semester_label": semester_label,
                      "reason": "Trained table position not found for this semester (vertical layout)."}]
    grid = expand_table_grid(chunk[roles["position"]])

    subjects = load_subjects(semester_label, db_path)
    nodes = load_component_template(semester_label, db_path)
    nodes_by_id = {n["node_id"]: n for n in nodes}

    leaf_by_path = {}
    for n in leaf_nodes(nodes):
        path = []
        cur = n
        while cur is not None:
            path.append(cur["label"].strip().upper())
            cur = nodes_by_id.get(cur["parent_id"]) if cur["parent_id"] is not None else None
        leaf_by_path[tuple(reversed(path))] = n

    subjects_by_name = {s["subject_name"].strip().upper(): s for s in subjects}
    level_cols = roles["level_cols"]

    records = []
    review = []
    current_subject = None
    last_values = [None] * len(level_cols)
    for r in range(roles["row_start"], roles["row_end"] + 1):
        title = _cell(grid, r, roles["title_col"])
        if title:
            match = subjects_by_name.get(title.strip().upper())
            if match is None and title.strip().upper() not in subjects_by_name:
                # Could be a genuinely new/renamed subject on this
                # student's page -- flag it rather than silently
                # dropping their marks for it.
                review.append({"enrollment": enrollment, "semester_label": semester_label,
                                "reason": f"Row with subject title '{title}' doesn't match any subject "
                                          f"trained for this semester -- its marks were skipped."})
            if match is not current_subject:
                last_values = [None] * len(level_cols)  # new subject block -- don't carry over
            current_subject = match
        if current_subject is None:
            continue
        # Forward-fill a blank level cell from the last non-blank value in
        # that column (within this subject) -- mirrors build_vertical_template's
        # fill, since the same merged/rowspan Level-1 cell that doesn't
        # repeat during training won't repeat here either.
        raw = [_cell(grid, r, c) for c in level_cols]
        filled = []
        for i, v in enumerate(raw):
            if v:
                last_values[i] = v
                filled.append(v)
            else:
                filled.append(last_values[i])
        if not all(filled):
            review.append({"enrollment": enrollment, "semester_label": semester_label,
                            "reason": f"Row {r} for subject '{current_subject['subject_name']}' has a "
                                      f"blank Level-column value (raw: {tuple(raw)}) with nothing to "
                                      f"carry forward -- that row's marks were skipped."})
            continue
        path = tuple(v.upper() for v in filled)
        leaf = leaf_by_path.get(path)
        if leaf is None:
            known = sorted(" > ".join(p) for p in leaf_by_path.keys())
            review.append({"enrollment": enrollment, "semester_label": semester_label,
                            "reason": f"Row {r} for subject '{current_subject['subject_name']}' has "
                                      f"component path {' > '.join(path)} which was never seen during "
                                      f"training (trained paths: {known}) -- that row's marks were skipped."})
            continue
        label = node_path_label(leaf["node_id"], nodes_by_id)
        max_val = _cell(grid, r, roles["max_col"])
        obt_val = _cell(grid, r, roles["obt_col"])
        records.append({"enrollment": enrollment, "semester_label": semester_label,
                         "subject_index": current_subject["subject_index"],
                         "subject_name": current_subject["subject_name"],
                         "node_id": leaf["node_id"], "component_label": label,
                         "role": "max", "value": max_val})
        records.append({"enrollment": enrollment, "semester_label": semester_label,
                         "subject_index": current_subject["subject_index"],
                         "subject_name": current_subject["subject_name"],
                         "node_id": leaf["node_id"], "component_label": label,
                         "role": "obtained", "value": obt_val})
    return records, review


def extract_subjectwise_from_chunk(chunk, semester_label, enrollment, db_path=DB_FILE):
    """Scheme-agnostic extraction, v2: for every subject and every leaf
    that's enabled for that subject, read back the trained Max/Obtained
    cells. No branching on scheme/layout -- just plays back what Step 1-6
    trained. Returns (records, review). Loads the template/subjects/
    disabled/values fresh each call -- fine for extract-mode's per-
    enrollment loop, since these are small semester-scoped tables."""
    subjects = load_subjects(semester_label, db_path)
    nodes = load_component_template(semester_label, db_path)
    nodes_by_id = {n["node_id"]: n for n in nodes}
    disabled_set = load_subject_node_disabled(semester_label, db_path)
    values = load_subject_node_values(semester_label, db_path)
    leaves = leaf_nodes(nodes)
    leaf_ids = {n["node_id"] for n in leaves}

    records = []
    review = []
    grids = {}

    def get_grid(pos):
        if pos not in grids:
            if pos >= len(chunk):
                grids[pos] = None
            else:
                grids[pos] = expand_table_grid(chunk[pos])
        return grids[pos]

    subjects_by_idx = {s["subject_index"]: s for s in subjects}
    for v in values:
        if v["node_id"] not in leaf_ids:
            continue
        subj = subjects_by_idx.get(v["subject_index"])
        if subj is None:
            continue
        if not node_enabled_for_subject(v["node_id"], v["subject_index"], nodes_by_id, disabled_set):
            continue
        grid = get_grid(v["position"])
        label = node_path_label(v["node_id"], nodes_by_id)
        if grid is None:
            review.append({"enrollment": enrollment, "semester_label": semester_label,
                            "reason": f"Trained table position {v['position']} not found for '{label}'."})
            continue
        r, c = v["abs_row"], v["abs_col"]
        if r >= len(grid) or c >= len(grid[r]):
            review.append({"enrollment": enrollment, "semester_label": semester_label,
                            "reason": f"'{subj['subject_name']}' / {label} ({v['role']}): cell ({r},{c}) out of "
                                      f"bounds -- layout may have shifted, re-run train mode."})
            continue
        records.append({
            "enrollment": enrollment, "semester_label": semester_label,
            "subject_index": v["subject_index"], "subject_name": subj["subject_name"],
            "node_id": v["node_id"], "component_label": label, "role": v["role"],
            "value": grid[r][c],
        })

    return records, review


# ==========================================================
# OFFLINE IMPORT (fallback when MSBTE's site/data is unavailable)
# ==========================================================
# Reuses every table Train mode + Extract mode already write to --
# subjects / component_template / semester_template_settings /
# subject_node_disabled / subject_node_values for STRUCTURE (Train
# mode's job), and student_records / subjectwise_student_records for
# DATA (Extract mode's job). Only the SOURCE differs: instead of
# dragging over live HTML (Train) or scraping live HTML per enrollment
# (Extract), structure is typed once (header block) and data is pasted
# in bulk (data block). Every semester imported this way is treated as
# FIXED-POSITION/K-scheme-shaped -- subjectwise_vertical_roles is never
# used here, even if "levels vary per subject" (that's handled by the
# same shared-template + per-subject-disabled-leaves mechanism Train
# mode's horizontal engine already uses -- see
# node_enabled_for_subject()/subject_node_disabled above).

# The per-student columns pasted alongside the subject marks --
# Institute Name/Address/Year/Program/Semester are all deliberately
# excluded here: they're COMMON fields, typed once for the whole import
# (Institute Name/Address are global report_settings, same as Train
# mode's boxes; Year/Program/Semester are chosen once per import on the
# Offline Import setup screen) rather than repeated identically down
# every single row of the paste.
OFFLINE_IDENTITY_GROUPS = ["name", "enrollment_number", "seat_number"]
OFFLINE_SUMMARY_GROUPS = ["total_marks", "obtained_total_marks", "percentage", "result"]
OFFLINE_ROW_GROUPS = OFFLINE_IDENTITY_GROUPS + OFFLINE_SUMMARY_GROUPS


def build_offline_template(subjects_spec):
    """subjects_spec: list of dicts, one per subject, in left-to-right
    order, each: {"name": str, "level_labels": [[label]*leaf_count, ...]
    -- one list per level, "max_values": [str]*leaf_count}.

    Builds ONE shared component tree across every subject (a leaf at the
    same tree position -- same label chain -- in two different subjects
    reuses the same node_id, exactly like a semester trained once online
    and reused for every subject), and per-subject disabled-node pairs
    for any node a given subject never touches -- this is what lets
    levels/leaf-count genuinely vary per subject while every subject
    still shares one template, same as node_enabled_for_subject() already
    expects.

    Returns {"subjects", "nodes", "max_levels", "disabled_pairs",
    "node_values", "leaf_columns"} -- leaf_columns is the ordered list of
    (subject, leaf) columns, in the SAME left-to-right order the pasted
    data's columns must follow.
    """
    subjects = []
    nodes = []
    node_values = []
    leaf_columns = []
    trie = {}  # (parent_id, level, label) -> node_id
    next_id = [1]
    used_by_subject = []  # index-aligned with subjects_spec: set of node_ids

    for subj_idx, spec in enumerate(subjects_spec):
        subjects.append({
            "index": subj_idx, "name": spec["name"], "position": 0,
            "abs_row": subj_idx, "abs_col": 0,
        })
        level_labels = spec["level_labels"]
        leaf_count = len(spec["max_values"])
        used_nodes = set()
        for leaf_i in range(leaf_count):
            parent_id = None
            chain_ids = []
            chain_labels = []
            for level_idx, labels_for_level in enumerate(level_labels):
                label = (labels_for_level[leaf_i] or "").strip()
                key = (parent_id, level_idx, label)
                if key not in trie:
                    node_id = next_id[0]
                    next_id[0] += 1
                    trie[key] = node_id
                    nodes.append({
                        "node_id": node_id, "parent_id": parent_id,
                        "level": level_idx + 1, "label": label,
                    })
                node_id = trie[key]
                chain_ids.append(node_id)
                chain_labels.append(label)
                parent_id = node_id
            used_nodes.update(chain_ids)
            leaf_node_id = chain_ids[-1]
            node_values.append({
                "subject_index": subj_idx, "node_id": leaf_node_id, "role": "max",
                "position": 0, "abs_row": subj_idx, "abs_col": leaf_i,
            })
            leaf_columns.append({
                "subject_index": subj_idx, "subject_name": spec["name"],
                "node_id": leaf_node_id,
                "component_label": " / ".join(l for l in chain_labels if l),
                "max_value": (spec["max_values"][leaf_i] or "").strip(),
            })
        used_by_subject.append(used_nodes)

    all_node_ids = {n["node_id"] for n in nodes}
    disabled_pairs = [
        (subj_idx, node_id)
        for subj_idx, used_nodes in enumerate(used_by_subject)
        for node_id in (all_node_ids - used_nodes)
    ]
    max_levels = max((len(s["level_labels"]) for s in subjects_spec), default=1)

    return {
        "subjects": subjects, "nodes": nodes, "max_levels": max_levels,
        "disabled_pairs": disabled_pairs, "node_values": node_values,
        "leaf_columns": leaf_columns,
    }


def save_offline_structure_to_db(semester_label, template, db_path=DB_FILE):
    """Writes the header-block structure (Step 1 of offline import) into
    the exact same tables Train mode's horizontal engine writes to --
    see finalize_subjectwise_training_horizontal(). Retrain-safe: wholly
    replaces this semester's structure, same as re-running Train mode."""
    init_db(db_path)
    save_subjects_to_db(semester_label, template["subjects"], db_path)
    save_component_template_to_db(semester_label, template["nodes"], db_path)
    save_component_template_settings(semester_label, template["max_levels"], db_path)
    save_subject_node_disabled(semester_label, template["disabled_pairs"], db_path)
    save_subject_node_values_to_db(semester_label, template["node_values"], db_path)
    # Fixed-position only -- never leave a stale vertical-mode row behind
    # for this semester (see the matching cleanup in the horizontal/
    # vertical Train-mode finalizers).
    conn = sqlite3.connect(db_path)
    conn.execute("DELETE FROM subjectwise_vertical_roles WHERE semester_label = ?", (semester_label,))
    conn.commit()
    conn.close()


def parse_pasted_grid(text):
    """Splits a block of text copy-pasted from Excel into rows of cells.
    Excel's clipboard format is tab-separated columns, newline-separated
    rows -- exactly what a browser paste event delivers here too."""
    lines = [ln for ln in text.replace("\r\n", "\n").replace("\r", "\n").split("\n") if ln.strip() != ""]
    return [ln.split("\t") for ln in lines]


def save_offline_student_rows(semester_label, year, program, leaf_columns, rows, db_path=DB_FILE):
    """Writes the data-block rows (Step 2 of offline import) into
    student_records + subjectwise_student_records -- the exact tables
    Extract mode writes to. Each row must have
    len(OFFLINE_ROW_GROUPS) + len(leaf_columns) cells, in that order:
    Name, Enrollment Number, Seat Number, Total Marks, Obtained Total
    Marks, Percentage, Result, then one cell per leaf column (matching
    build_offline_template()'s leaf_columns order).

    year/program are COMMON fields -- typed once on the Offline Import
    setup screen, not part of the pasted row -- and get written the same
    constant value for every student here, same as "semester" already is.

    Returns (saved_count, errors) -- a row with the wrong cell count or a
    blank enrollment number is skipped and reported, not silently dropped
    or allowed to corrupt other rows.
    """
    init_db(db_path)
    expected_len = len(OFFLINE_ROW_GROUPS) + len(leaf_columns)
    enr_idx = OFFLINE_ROW_GROUPS.index("enrollment_number")

    identity_records = []
    subjectwise_records = []
    errors = []
    saved = 0

    for r_i, row in enumerate(rows):
        if len(row) < expected_len:
            errors.append(
                f"Row {r_i + 1}: expected {expected_len} columns, found {len(row)} -- skipped"
            )
            continue
        enrollment = (row[enr_idx] or "").strip()
        if not enrollment:
            errors.append(f"Row {r_i + 1}: blank Enrollment Number -- skipped")
            continue

        for g_i, group in enumerate(OFFLINE_ROW_GROUPS):
            identity_records.append({
                "enrollment": enrollment, "semester_label": semester_label,
                "group_name": group, "field_name": group,
                "range_idx": 0, "row_offset": 0, "col_offset": 0,
                "abs_row": 0, "abs_col": g_i, "value": (row[g_i] or "").strip(),
            })
        # "semester"/"year"/"program" aren't pasted columns -- every row
        # in this batch belongs to the one semester/year/program chosen
        # once for the whole import. Still saved per-student so
        # get_semester_identity_text() and anything else reading these
        # group_names keeps working exactly as it does for online data.
        for group, value in (("semester", semester_label), ("year", year), ("program", program)):
            identity_records.append({
                "enrollment": enrollment, "semester_label": semester_label,
                "group_name": group, "field_name": group,
                "range_idx": 0, "row_offset": 0, "col_offset": 0,
                "abs_row": 0, "abs_col": {"semester": -1, "year": -2, "program": -3}[group],
                "value": value,
            })

        for l_i, col in enumerate(leaf_columns):
            value = (row[len(OFFLINE_ROW_GROUPS) + l_i] or "").strip()
            subjectwise_records.append({
                "enrollment": enrollment, "semester_label": semester_label,
                "subject_index": col["subject_index"], "subject_name": col["subject_name"],
                "node_id": col["node_id"], "component_label": col["component_label"],
                "role": "obtained", "value": value,
            })
            # Max marks are constant per (subject, leaf), not typed per
            # student -- but build_semester_structure_subjectwise() reads
            # role='max' out of subjectwise_student_records (same as a
            # live extract writes it per-enrollment, see
            # extract_subjectwise_from_chunk()), so the same Max value
            # from the header block is repeated onto every student's row
            # here too, to match that read path exactly.
            subjectwise_records.append({
                "enrollment": enrollment, "semester_label": semester_label,
                "subject_index": col["subject_index"], "subject_name": col["subject_name"],
                "node_id": col["node_id"], "component_label": col["component_label"],
                "role": "max", "value": col.get("max_value", ""),
            })
        saved += 1

    save_records_to_db(identity_records, [], db_path)
    save_subjectwise_student_records_to_db(subjectwise_records, db_path)
    return saved, errors


def save_subjectwise_student_records_to_db(records, db_path=DB_FILE):
    conn = sqlite3.connect(db_path)
    for rec in records:
        conn.execute(
            "INSERT INTO subjectwise_student_records "
            "(enrollment, semester_label, subject_index, subject_name, node_id, component_label, role, value) "
            "VALUES (?,?,?,?,?,?,?,?) "
            "ON CONFLICT(enrollment, semester_label, subject_index, node_id, role) "
            "DO UPDATE SET value=excluded.value",
            (rec["enrollment"], rec["semester_label"], rec["subject_index"], rec["subject_name"],
             rec["node_id"], rec["component_label"], rec["role"], rec["value"]),
        )
    conn.commit()
    conn.close()


# ==========================================================
# SCHEME SUPPORT (K-scheme vs I-scheme vs future schemes)
# ==========================================================
# MSBTE has changed the marks-statement layout at least once (K-scheme ->
# I-scheme) and will likely change it again. The two layouts aren't just
# different coordinates -- they're different table GRAMMARS:
#
#   K-scheme: one row per subject. FA-TH/SA-TH/FA-PR/SA-PR/SLA are
#             COLUMNS. Subject count varies, column layout never does.
#             -> "grid-fixed" extraction (the original GROUPS/DYNAMIC_GROUPS
#                machinery below, UNCHANGED).
#
#   I-scheme: 2 to 4 ROWS per subject (TH-PA, TH-ESE, PR-PA, PR-ESE --
#             only the rows that apply to that subject are present, so
#             row count varies PER SUBJECT, not just per student). The
#             component identity (TH/PR, PA/ESE) lives IN the row, not
#             in a fixed column position.
#             -> "label-driven" extraction: walk the grid row by row,
#                using a handful of trained COLUMN indices (title,
#                component, subcomponent, marks) rather than a row
#                rectangle, and let subject boundaries fall out of where
#                the title column's value changes.
#
# A new scheme in future only needs: (1) a signature in SCHEME_SIGNATURES,
# (2) a groups list + extractor if its grammar doesn't match either
# existing one, (3) an entry in *_COMPONENT_MAP. Report/eligibility code
# should read from canonical_marks (see normalize_*_to_canonical below)
# so it never has to change per scheme.

DEFAULT_SCHEME = "k_scheme"

# Role-columns needed to walk an I-scheme subject block. Unlike GROUPS
# (K-scheme), these aren't row/col rectangles -- in train mode each is a
# SINGLE column, so the user just clicks one representative data cell per
# role instead of dragging a range. "title" additionally supplies the row
# to start scanning from (its trained row_start).
I_SCHEME_GROUPS = [
    ("title", "Course/Subject Name (click any one subject-name cell)"),
    ("th_pr", "TH / PR indicator column"),
    ("course_head", "Course Head column (ESE / PA)"),
    ("max_marks", "Max Marks column"),
    ("min_marks", "Min Marks column"),
    ("obtained_marks", "Marks Obtained column"),
    ("total_max_marks", "Total Max Marks column"),
    ("total_obtained_marks", "Total Marks Obtained column"),
    ("credits", "Credits column"),
]
I_SCHEME_REQUIRED_GROUPS = {"title", "th_pr", "course_head", "obtained_marks"}

# Signature check run against the flattened, upper-cased text of a
# candidate marks table's first few rows. First match wins. If NOTHING
# matches, the sheet is a layout the tool has never seen -- it should be
# flagged for review rather than silently mis-extracted with the wrong
# scheme's rules.
SCHEME_SIGNATURES = {
    "k_scheme": lambda cells: {"FA-TH", "SA-TH"} <= cells or {"FA-PR", "SA-PR"} <= cells,
    "i_scheme": lambda cells: {"COURSE HEAD"} <= cells and ({"TH/PR"} <= cells or {"TH / PR"} <= cells),
}


def detect_scheme(table_grid):
    """Inspect a marks table's own header cells and return the scheme id
    ("k_scheme", "i_scheme", ...) or None if unrecognized. Deliberately a
    property of the SHEET, not of a saved config -- during a transition
    year the same semester_label can show up in both schemes across
    different students, and this must tell them apart per student."""
    cells = {c.strip().upper() for row in table_grid[:6] for c in row if c and c.strip()}
    for scheme_id, check in SCHEME_SIGNATURES.items():
        try:
            if check(cells):
                return scheme_id
        except Exception:
            continue
    return None


# Canonical, scheme-agnostic component vocabulary. Every downstream
# consumer (percentage fallback, eligibility, K7 reports, ...) should
# eventually be migrated to read canonical_marks / this vocabulary instead
# of raw group_name, so a future scheme change only touches this map, not
# report code.
CANONICAL_COMPONENTS = [
    "TH_INTERNAL", "TH_EXTERNAL", "TH_TOTAL",
    "PR_INTERNAL", "PR_EXTERNAL", "PR_TOTAL",
    "SLA", "SUBJECT_TOTAL",
]

# K-scheme: FA/SA columns map straight across.
K_SCHEME_COMPONENT_MAP = {
    "FA-TH": "TH_INTERNAL", "SA-TH": "TH_EXTERNAL",
    "FA-PR": "PR_INTERNAL", "SA-PR": "PR_EXTERNAL",
    "SLA": "SLA",
}

# I-scheme: (course_head_upper, th_pr_upper) pair -> canonical component.
I_SCHEME_COMPONENT_MAP = {
    ("PA", "TH"): "TH_INTERNAL", ("ESE", "TH"): "TH_EXTERNAL",
    ("PA", "PR"): "PR_INTERNAL", ("ESE", "PR"): "PR_EXTERNAL",
    ("PA", "TW"): "SLA", ("ESE", "TW"): "SLA",
    ("PA", "OR"): "SLA", ("ESE", "OR"): "SLA",
}


def extract_i_scheme_subjects(grid, spec):
    """Walk an I-scheme marks grid using trained COLUMN roles (spec =
    {"title": {"ranges": [{"col_start": c, "row_start": r, ...}]}, ...})
    and return a list of subjects, each with its component rows:
        [{"subject_name": "...", "components": [
            {"th_pr": "TH", "course_head": "PA", "max": "30", "min": "0",
             "obtained": "28", "total_max": "...", "total_obtained": "...",
             "credits": "..."}, ...]}, ...]

    Subject boundaries fall out of the title column's value changing --
    expand_table_grid() has already repeated a merged (rowspan) title
    cell's text into every row it spans, so this needs no rowspan
    handling of its own. Works regardless of whether a subject has 2
    rows (PR only) or 4 rows (TH + PR) or more.
    """
    def col_of(group_name, required=True):
        g = spec.get(group_name)
        if not g or not g.get("ranges"):
            if required:
                raise ValueError(f"I-scheme mapping is missing a trained column for '{group_name}'.")
            return None
        return g["ranges"][0]["col_start"]

    title_col = col_of("title")
    start_row = spec["title"]["ranges"][0].get("row_start", 0)
    th_pr_col = col_of("th_pr")
    course_head_col = col_of("course_head")
    max_col = col_of("max_marks", required=False)
    min_col = col_of("min_marks", required=False)
    obt_col = col_of("obtained_marks")
    total_max_col = col_of("total_max_marks", required=False)
    total_obt_col = col_of("total_obtained_marks", required=False)
    credits_col = col_of("credits", required=False)

    def cell(row, col):
        if col is None or col >= len(row):
            return ""
        return row[col].strip()

    subjects = []
    current = None
    for row in grid[start_row:]:
        if not row or all(not v.strip() for v in row):
            continue
        title = cell(row, title_col)
        th_pr = cell(row, th_pr_col).upper()
        course_head = cell(row, course_head_col).upper()

        if not th_pr and not course_head:
            # Neither role column has data on this row -- not a subject
            # component row (could be a trailing/blank/footer row).
            continue

        if title and (current is None or title != current["subject_name"]):
            current = {"subject_name": title, "components": []}
            subjects.append(current)

        if current is None:
            # Component row appeared before any title was seen -- treat
            # as unattributed rather than guessing which subject it
            # belongs to.
            continue

        current["components"].append({
            "th_pr": th_pr,
            "course_head": course_head,
            "max": cell(row, max_col),
            "min": cell(row, min_col),
            "obtained": cell(row, obt_col),
            "total_max": cell(row, total_max_col),
            "total_obtained": cell(row, total_obt_col),
            "credits": cell(row, credits_col),
        })

    return subjects


def normalize_i_scheme_to_canonical(subjects, enrollment, semester_label):
    """subjects = output of extract_i_scheme_subjects(). Returns rows
    ready for canonical_marks: one row per (subject, canonical component)."""
    rows = []
    for subj in subjects:
        for comp in subj["components"]:
            canonical = I_SCHEME_COMPONENT_MAP.get((comp["course_head"], comp["th_pr"]))
            if canonical is None:
                continue  # unrecognized component combo -- surfaced via review, not silently dropped
            rows.append({
                "enrollment": enrollment, "semester_label": semester_label, "scheme": "i_scheme",
                "subject_name": subj["subject_name"], "component": canonical,
                "max_marks": comp["max"], "obtained_marks": comp["obtained"],
                "credits": comp["credits"],
            })
        # subject-level total, if the trained mapping captured total columns
        totals = [c for c in subj["components"] if c["total_max"] or c["total_obtained"]]
        if totals:
            last = totals[-1]
            rows.append({
                "enrollment": enrollment, "semester_label": semester_label, "scheme": "i_scheme",
                "subject_name": subj["subject_name"], "component": "SUBJECT_TOTAL",
                "max_marks": last["total_max"], "obtained_marks": last["total_obtained"],
                "credits": last["credits"],
            })
    return rows


def apply_i_scheme_mapping_to_chunk(chunk, label, spec, enrollment):
    """I-scheme counterpart to apply_mapping_to_chunk(). spec is the
    label-driven column-role mapping (see I_SCHEME_GROUPS). Returns
    (canonical_rows, review) instead of (extracted, review) -- I-scheme
    records go straight into canonical_marks rather than the raw
    grid-cell tables, since "abs_row/abs_col" isn't a meaningful concept
    for a layout with variable rows per subject."""
    review = []
    missing = I_SCHEME_REQUIRED_GROUPS - {g for g in spec if spec.get(g, {}).get("ranges")}
    if missing:
        review.append({"enrollment": enrollment, "semester_label": label,
                        "reason": f"I-scheme mapping missing required column(s): {', '.join(sorted(missing))}. "
                                  f"Re-run train mode for this semester."})
        return [], review

    marks_table = None
    for table in chunk:
        grid = expand_table_grid(table)
        if detect_scheme(grid) == "i_scheme":
            marks_table = grid
            break
    if marks_table is None:
        review.append({"enrollment": enrollment, "semester_label": label,
                        "reason": "Could not find an I-scheme marks table in this student's page "
                                  "(scheme signature not found in any table)."})
        return [], review

    try:
        subjects = extract_i_scheme_subjects(marks_table, spec)
    except ValueError as e:
        review.append({"enrollment": enrollment, "semester_label": label, "reason": str(e)})
        return [], review

    if not subjects:
        review.append({"enrollment": enrollment, "semester_label": label,
                        "reason": "I-scheme extraction found the marks table but no subject rows. "
                                  "Layout may have changed -- re-run train mode."})
        return [], review

    canonical_rows = normalize_i_scheme_to_canonical(subjects, enrollment, label)
    return canonical_rows, review


def normalize_k_scheme_to_canonical(extracted, enrollment, semester_label):
    """K-scheme counterpart, built from apply_mapping_to_chunk()'s output
    (the existing grid-cell records). Groups obtained_marks/maximum_marks
    cells by their row (= one subject) and column position (= one of the
    5 FA-TH/SA-TH/FA-PR/SA-PR/SLA components, in that trained column
    order) and maps each to the same canonical vocabulary I-scheme uses,
    via K_SCHEME_COMPONENT_MAP. This is what lets a report eventually be
    written once against canonical_marks and work for both schemes."""
    subjects_by_row = {}
    for rec in extracted:
        if rec["group_name"] == "subjects":
            subjects_by_row[rec["abs_row"]] = rec["value"]

    component_order = list(K_SCHEME_COMPONENT_MAP.keys())  # FA-TH, SA-TH, FA-PR, SA-PR, SLA
    obtained_by_row = {}
    max_by_row = {}
    for rec in extracted:
        if rec["group_name"] == "obtained_marks":
            obtained_by_row.setdefault(rec["abs_row"], {})[rec["col_offset"]] = rec["value"]
        elif rec["group_name"] == "maximum_marks":
            max_by_row.setdefault(rec["abs_row"], {})[rec["col_offset"]] = rec["value"]

    rows = []
    for abs_row, subject_name in subjects_by_row.items():
        obt_cols = obtained_by_row.get(abs_row, {})
        max_cols = max_by_row.get(abs_row, {})
        for col_offset, raw_component in enumerate(component_order):
            if col_offset not in obt_cols and col_offset not in max_cols:
                continue
            canonical = K_SCHEME_COMPONENT_MAP[raw_component]
            rows.append({
                "enrollment": enrollment, "semester_label": semester_label, "scheme": "k_scheme",
                "subject_name": subject_name, "component": canonical,
                "max_marks": max_cols.get(col_offset, ""), "obtained_marks": obt_cols.get(col_offset, ""),
                "credits": "",
            })
    return rows


def run_range_selector_dialog(semester_label, chunk, groups=None):
    """
    Shows EVERY table in this semester's group of tables exactly as it
    appears on the page -- no recategorizing into "heading/marks/
    summary", just Table 1, Table 2, Table 3, Table 4 (raw), in order.

    `groups` defaults to GROUPS (K-scheme's 15 fixed fields). Passing
    I_SCHEME_GROUPS reuses this exact same click/drag UI to train an
    I-scheme sheet instead -- for I-scheme groups, only ONE cell needs to
    be selected per group (a representative cell in that column); the
    label-driven extractor (extract_i_scheme_subjects) only reads
    col_start (the column) and, from the "title" group, row_start (where
    subject rows begin) -- it doesn't need a dragged rectangle. This is
    what makes adding a future scheme's groups a config change, not a UI
    rewrite: any new groups list works here without touching this dialog.

    Drag a rectangle in ANY of these tables, then click "Add to <group>"
    for whichever of the fixed groups it belongs to. For K-scheme's
    groups: Year, Program, Name, Enrollment Number, Seat Number,
    Semester, Subjects, Maximum Marks, Obtained Marks, THPRSLA, FASA,
    Total Marks, Obtained Total Marks, Percentage, Result (see GROUPS for
    the authoritative list/order -- Year comes first since every report
    heading needs it). You can add MULTIPLE rectangles to the same group
    (needed e.g. for Maximum Marks, since MAX/OBT columns alternate and
    aren't one contiguous block).

    Right below the Year group sits a completely different kind of
    input: two plain typed text boxes, Institute Name and Institute
    Address -- these don't come from anywhere on the MSBTE page, so
    there's nothing to drag a box around; the user just types them once.
    They're global (shared across every semester, not retrained each
    time) and get saved to report_settings as soon as this dialog is
    submitted, prefilled from whatever's already saved if this runs
    again later.

    Returns a dict: {group_name: {"ranges": [ {position_in_group,
    row_start, row_end, col_start, col_end, expected_num_cols}, ... ]}}
    Only groups with at least one range are included.
    """
    groups = groups if groups is not None else GROUPS

    root = tk.Toplevel(_get_app_root())
    root.title(f"Select ranges - {semester_label}")
    root.attributes("-topmost", True)
    root.geometry("1400x900")
    root.minsize(700, 400)
    try:
        root.state("zoomed")
    except tk.TclError:
        pass

    tk.Label(
        root,
        text=(f"{semester_label}: drag a rectangle in ANY table below (hold CTRL while dragging to add "
              "another range, like Excel -- useful for Maximum Marks/Obtained Marks, since MAX and OBT "
              "columns alternate). Once you've marked everything for one group, click its 'Add to ...' "
              "button -- all ranges you drew get saved together and the table clears, ready for the next group."),
        font=("Arial", 11, "bold"), justify="left",
    ).pack(padx=10, pady=(10, 5), anchor="w")

    # Main area: scrollable tables on the left, fixed vertical button panel
    # on the right (so the buttons stay put regardless of table scrolling).
    main_frame = tk.Frame(root)
    main_frame.pack(fill="both", expand=True)

    outer_canvas = tk.Canvas(main_frame)
    scrollbar = ttk.Scrollbar(main_frame, orient="vertical", command=outer_canvas.yview)
    scroll_frame = tk.Frame(outer_canvas)
    scroll_frame.bind("<Configure>", lambda e: outer_canvas.configure(scrollregion=outer_canvas.bbox("all")))
    outer_canvas.create_window((0, 0), window=scroll_frame, anchor="nw")
    outer_canvas.configure(yscrollcommand=scrollbar.set)
    outer_canvas.pack(side="left", fill="both", expand=True, padx=(10, 0), pady=5)
    scrollbar.pack(side="left", fill="y")

    def _on_mousewheel_left(event):
        outer_canvas.yview_scroll(int(-1 * (event.delta / 120)), "units")
    # Only capture the mouse wheel while hovering the tables area -- the
    # side panel gets its own independent scroll binding below.
    outer_canvas.bind("<Enter>", lambda e: outer_canvas.bind_all("<MouseWheel>", _on_mousewheel_left))
    outer_canvas.bind("<Leave>", lambda e: outer_canvas.unbind_all("<MouseWheel>"))

    # last-touched grid, shared across all tables via SelectableGrid's on_change
    last_active = {"grid": None}

    def on_grid_change(grid):
        last_active["grid"] = grid

    grids = []
    for pos, table in enumerate(chunk):
        grid_data = expand_table_grid(table)
        g = SelectableGrid(scroll_frame, grid_data, f"Table {pos + 1} (raw, {len(grid_data)} rows x "
                            f"{max((len(r) for r in grid_data), default=0)} cols)",
                            position=pos, on_change=on_grid_change)
        grids.append(g)

    # group_name -> list of (position_in_group, row_start, row_end, col_start, col_end, expected_num_cols)
    collected = {key: [] for key, _ in groups}
    check_labels = {}
    status_var = tk.StringVar(value="No ranges added yet.")

    def _refresh_status():
        parts = [f"{label}: {len(collected[key])}" for key, label in groups if collected[key]]
        status_var.set("Added so far -> " + (", ".join(parts) if parts else "(none)"))
        for key, _ in groups:
            check_labels[key].configure(text="\u2713" if collected[key] else "")

    def make_add_handler(group_key):
        def _add():
            grid = last_active["grid"]
            if grid is None or not grid.get_selections():
                messagebox.showinfo("No selection", "Drag a rectangle in one of the tables first "
                                                     "(hold CTRL to add more than one range).")
                return
            for (row_start, row_end, col_start, col_end) in grid.get_selections():
                collected[group_key].append((grid.position, row_start, row_end, col_start, col_end, grid.num_cols))
            grid.clear_selections()
            _refresh_status()
        return _add

    def make_clear_handler(group_key):
        def _clear():
            collected[group_key] = []
            _refresh_status()
        return _clear

    result = {}

    def submit():
        for group_key, _ in groups:
            rects = collected[group_key]
            if not rects:
                continue
            result[group_key] = {
                "ranges": [
                    {"position_in_group": pos, "row_start": r0, "row_end": r1,
                     "col_start": c0, "col_end": c1, "expected_num_cols": num_cols}
                    for (pos, r0, r1, c0, c1, num_cols) in rects
                ],
            }
        # Institute Name/Address are global (not per-semester), so these
        # save regardless of which/whether any page ranges were marked --
        # typing them once while training any semester is enough.
        name, address = institute_name_var.get().strip(), institute_address_var.get().strip()
        if name or address:
            save_report_settings({"institute_name": name, "institute_address": address}, DB_FILE)
        outer_canvas.unbind_all("<MouseWheel>")
        side_canvas.unbind_all("<MouseWheel>")
        root.destroy()

    # Fixed right-side panel: one row per group, stacked vertically. Each
    # row shows "Add to <group>", a tick mark that appears once at least
    # one range has been added for that group, and a "Clear" button.
    # Wrapped in its own canvas + vertical scrollbar (slider) so all 7
    # groups stay reachable even if the window is short.
    side_outer = tk.Frame(main_frame, relief="groove", bd=1)
    side_outer.pack(side="right", fill="y", padx=(10, 10), pady=5)

    side_canvas = tk.Canvas(side_outer, width=220, highlightthickness=0)
    side_scrollbar = ttk.Scrollbar(side_outer, orient="vertical", command=side_canvas.yview)
    side_panel = tk.Frame(side_canvas)
    side_panel.bind("<Configure>", lambda e: side_canvas.configure(scrollregion=side_canvas.bbox("all")))
    side_canvas.create_window((0, 0), window=side_panel, anchor="nw")
    side_canvas.configure(yscrollcommand=side_scrollbar.set)
    side_canvas.pack(side="left", fill="both", expand=True)
    side_scrollbar.pack(side="right", fill="y")

    def _on_mousewheel_right(event):
        side_canvas.yview_scroll(int(-1 * (event.delta / 120)), "units")
    side_canvas.bind("<Enter>", lambda e: side_canvas.bind_all("<MouseWheel>", _on_mousewheel_right))
    side_canvas.bind("<Leave>", lambda e: side_canvas.unbind_all("<MouseWheel>"))

    tk.Label(side_panel, text="Groups", font=("Arial", 10, "bold")).pack(anchor="w", padx=6, pady=(8, 6))

    existing_settings = load_report_settings(DB_FILE)
    institute_name_var = tk.StringVar(value=existing_settings.get("institute_name", ""))
    institute_address_var = tk.StringVar(value=existing_settings.get("institute_address", ""))

    for idx, (key, label) in enumerate(groups, start=1):
        box = tk.Frame(side_panel, relief="groove", bd=2)
        box.pack(fill="x", padx=6, pady=(0, 8))

        header = tk.Frame(box)
        header.pack(fill="x", padx=6, pady=(6, 2))
        tk.Label(header, text=f"{idx}. {label}", font=("Arial", 9, "bold")).pack(side="left")
        check = tk.Label(header, text="", font=("Arial", 11, "bold"), fg="#1a9c1a", width=2)
        check.pack(side="right")
        check_labels[key] = check

        ttk.Button(box, text="Add", command=make_add_handler(key)).pack(fill="x", padx=6, pady=(0, 3))
        ttk.Button(box, text="Clear", command=make_clear_handler(key)).pack(fill="x", padx=6, pady=(0, 6))

        if key == "year":
            # Not a page range like the groups above/below -- plain typed
            # text, saved once and reused on every report's heading
            # (Institute Name/Address don't appear anywhere on the MSBTE
            # result page itself, so there's nothing to drag a box around).
            info_box = tk.Frame(side_panel, relief="groove", bd=2)
            info_box.pack(fill="x", padx=6, pady=(0, 8))
            tk.Label(info_box, text="Institute Name && Address", font=("Arial", 9, "bold")).pack(
                anchor="w", padx=6, pady=(6, 2))
            tk.Label(info_box, text="(typed once, reused on every report --\nnot selected from the page)",
                     font=("Arial", 7), fg="#666666", justify="left").pack(anchor="w", padx=6)
            tk.Label(info_box, text="Institute Name:", font=("Arial", 8)).pack(anchor="w", padx=6, pady=(6, 0))
            tk.Entry(info_box, textvariable=institute_name_var).pack(fill="x", padx=6, pady=(0, 4))
            tk.Label(info_box, text="Institute Address:", font=("Arial", 8)).pack(anchor="w", padx=6)
            tk.Entry(info_box, textvariable=institute_address_var).pack(fill="x", padx=6, pady=(0, 6))

    tk.Label(side_panel, textvariable=status_var, font=("Arial", 8), fg="#444444",
             justify="left", wraplength=190, anchor="w").pack(fill="x", padx=6, pady=(4, 12))

    ttk.Button(side_panel, text="Save these ranges\nfor this semester", command=submit).pack(fill="x", padx=6, pady=(0, 10))

    root.grab_set()
    root.wait_window()
    return result


def detect_scheme_in_chunk(chunk):
    """Try every table in a student's table-group and return the scheme
    id detected from whichever one matches a signature (the marks table
    is usually chunk[1], but this doesn't assume a fixed position)."""
    for table in chunk:
        scheme_id = detect_scheme(expand_table_grid(table))
        if scheme_id:
            return scheme_id
    return None


def load_mapping():
    """Loads MAPPING_FILE as {scheme_id: {semester_label: entry}}.
    Transparently upgrades an old flat {semester_label: entry} file
    (pre-scheme-support, i.e. K-scheme-only) by nesting it under
    "k_scheme" -- existing trained mappings keep working with zero
    manual migration."""
    if not os.path.exists(MAPPING_FILE):
        return {}
    with open(MAPPING_FILE, encoding="utf-8") as f:
        raw = json.load(f)
    if not raw:
        return {}
    # A scheme-namespaced file's top-level keys are scheme ids
    # ("k_scheme"/"i_scheme"). An old, pre-scheme-support flat file's
    # top-level keys are semester labels (e.g. "FIRST SEMESTER") -- treat
    # anything that isn't a recognized scheme id as the old format and
    # nest it under "k_scheme" (the only scheme that existed before this
    # change), so existing trained mappings keep working with zero manual
    # migration.
    KNOWN_SCHEMES = {"k_scheme", "i_scheme"}
    if set(raw.keys()) <= KNOWN_SCHEMES:
        return raw
    return {"k_scheme": raw}


def save_mapping(mapping):
    with open(MAPPING_FILE, "w", encoding="utf-8") as f:
        json.dump(mapping, f, indent=2, ensure_ascii=False)


def run_train_mode():
    enrollments = ask_enrollment_numbers()
    if not enrollments:
        print("No enrollment numbers entered. Nothing to do.")
        return

    session = requests.Session()
    samples = {}  # semester_label -> [(enrollment, chunk), ...]

    for enr in enrollments:
        print(f"\nFetching {enr} ...")
        html = fetch_result_html(session, enr)
        if not html:
            print(f"  Skipped {enr} (fetch/captcha failed).")
            continue

        soup = BeautifulSoup(html, "html.parser")
        tables = soup.find_all("table")
        chunks = group_tables(tables)
        if not chunks:
            print(f"  No result tables found for {enr}. Wrong enrollment number, or no result available.")
            continue

        found_labels = []
        for chunk in chunks:
            header_grid = expand_table_grid(chunk[0])
            label = extract_semester_label(header_grid)
            if not label:
                continue
            samples.setdefault(label, []).append((enr, chunk))
            found_labels.append(label)
        print(f"  Found: {', '.join(found_labels) if found_labels else '(none)'}")

    if not samples:
        print("\nNo semester data collected from any enrollment number. Nothing to train.")
        return

    warnings = cross_check_samples(samples)
    if warnings:
        msg = "\n\n".join(warnings)
        print("\nSHAPE MISMATCH WARNINGS:\n" + msg)
        try:
            messagebox.showwarning(
                "Shape mismatch between samples",
                "Some semesters look different across your sample enrollments:\n\n" + msg +
                "\n\nYou can still continue -- the FIRST sample for each semester will be used "
                "for row selection -- but double-check this is expected.",
            )
        except tk.TclError:
            pass

    # Detect scheme PER LABEL from its own sample (not assumed globally),
    # so training a mix of K-scheme and I-scheme semesters in one run
    # (e.g. lower semesters already on the old scheme, higher semesters
    # on the new one) just works.
    mapping = load_mapping()
    scheme_by_label = {}
    for label, entries in samples.items():
        enr, chunk = entries[0]
        scheme_id = detect_scheme_in_chunk(chunk)
        if scheme_id is None:
            print(f"\n  '{label}' (sample from {enr}): could not detect a known scheme signature -- "
                  f"skipping. This may be a layout the tool hasn't seen before; check "
                  f"SCHEME_SIGNATURES in msbte_tool.py.")
            continue
        scheme_by_label[label] = scheme_id
        groups = GROUPS if scheme_id == "k_scheme" else I_SCHEME_GROUPS
        print(f"\nOpening range selector for {label} (scheme: {scheme_id}, sample from {enr}) ...")
        selection = run_range_selector_dialog(label, chunk, groups=groups)
        entry = {k: v for k, v in selection.items() if v is not None}
        if entry:
            mapping.setdefault(scheme_id, {})[label] = entry
            print(f"  Ranges saved for {label}: {list(entry.keys())}")
        else:
            print(f"  No ranges selected for {label}, skipping.")

    save_mapping(mapping)

    print(f"\nSaved mapping: {MAPPING_FILE}")
    for scheme_id, by_label in mapping.items():
        for label, entry in by_label.items():
            print(f"  [{scheme_id}] {label}: {list(entry.keys())}")

    # --- Save each semester's heading facts to the database, built right
    # here from the very sample you trained on, so it's deterministic --
    # these don't depend on whichever enrollment happens to be fetched
    # first during extract. K-scheme: unchanged, goes to semester_headings.
    # I-scheme: goes to canonical_marks (see apply_i_scheme_mapping_to_chunk). ---
    ordered_labels = [l for l in SEMESTER_NAMES if l in scheme_by_label]
    ordered_labels += [l for l in scheme_by_label if l not in SEMESTER_NAMES]

    for label in ordered_labels:
        scheme_id = scheme_by_label[label]
        if label not in mapping.get(scheme_id, {}):
            continue
        sample_enr, sample_chunk = samples[label][0]
        if scheme_id == "k_scheme":
            sample_extracted, _ = apply_mapping_to_chunk(sample_chunk, label, mapping[scheme_id][label], sample_enr)
            save_semester_headings_to_db(sample_extracted, label, DB_FILE)
        else:
            canonical_rows, review = apply_i_scheme_mapping_to_chunk(
                sample_chunk, label, mapping[scheme_id][label], sample_enr)
            if review:
                for r in review:
                    print(f"  [{label}] {r['reason']}")
            save_canonical_marks_to_db(canonical_rows, DB_FILE)

    if ordered_labels:
        print(f"Saved semester headings to database: {DB_FILE}")


# ==========================================================
# EXTRACT MODE
# ==========================================================

def apply_mapping_to_chunk(chunk, label, spec, enrollment):
    """Extract records for ONE already-matched (label, chunk) pair, given
    that semester's trained spec (mapping[label]). Used by both extract
    mode (chunk comes from a freshly parsed HTML page) and train mode
    (chunk is the very sample already sitting in memory from training --
    no re-fetch/re-parse needed to build that semester's headings sheet)."""
    extracted = []
    review = []

    for group_name, group_spec in spec.items():
        for range_idx, rng in enumerate(group_spec["ranges"]):
            pos = rng["position_in_group"]
            expected_cols = rng["expected_num_cols"]
            col_start, col_end = rng["col_start"], rng["col_end"]
            row_start, row_end = rng["row_start"], rng["row_end"]

            if pos >= len(chunk):
                review.append({"enrollment": enrollment, "semester_label": label,
                                "reason": f"'{group_name}' range #{range_idx}: expected table position {pos}, group only has {len(chunk)}."})
                continue

            grid = expand_table_grid(chunk[pos])
            actual_cols = len(grid[0]) if grid else 0

            if actual_cols != expected_cols:
                review.append({"enrollment": enrollment, "semester_label": label,
                                "reason": f"'{group_name}' range #{range_idx}: expected {expected_cols} columns in table {pos + 1}, "
                                          f"found {actual_cols}. Layout may have changed -- re-run train mode."})
                continue

            if group_name in DYNAMIC_GROUPS:
                # subject count varies per student, so extend down from
                # row_start as far as rows still look like data.
                r = row_start
                actual_end = row_start - 1
                while r < len(grid) and is_data_row(grid[r]):
                    actual_end = r
                    r += 1
                if actual_end < row_start:
                    review.append({"enrollment": enrollment, "semester_label": label,
                                    "reason": f"'{group_name}' range #{range_idx}: no data rows found starting at row {row_start}."})
                    continue
                row_end = actual_end
            else:
                if row_end >= len(grid):
                    review.append({"enrollment": enrollment, "semester_label": label,
                                    "reason": f"'{group_name}' range #{range_idx}: expected up to row {row_end}, table only has {len(grid)} row(s)."})
                    continue

            for r_offset, r in enumerate(range(row_start, row_end + 1)):
                row = grid[r]
                for c_offset, c in enumerate(range(col_start, min(col_end, len(row) - 1) + 1)):
                    extracted.append({
                        "enrollment": enrollment, "semester_label": label,
                        "field_name": f"{group_name}_g{range_idx}_r{r_offset}_c{c_offset}",
                        "value": row[c],
                        "group_name": group_name,
                        "range_idx": range_idx,
                        "row_offset": r_offset,
                        "col_offset": c_offset,
                        "abs_row": r,
                        "abs_col": c,
                    })

    return extracted, review


def apply_mapping_to_html(html, mapping, enrollment, db_path=DB_FILE):
    """Returns (extracted_records, canonical_rows, subjectwise_records,
    review_records) for one student's page. `mapping` is the
    SCHEME-NAMESPACED mapping from load_mapping():
    {"k_scheme": {label: spec}, "i_scheme": {label: spec}}.

    Each table-group's scheme is detected independently (detect_scheme_in_chunk)
    rather than assumed from the tool's config, so one student's page can
    mix schemes across semesters (a real scenario during a K-scheme ->
    I-scheme transition year) without any special-casing here.

    K-scheme keeps writing to `extracted` (one atomic grid-cell record per
    field, e.g. field_name="subjects_r3_c7") exactly as before -- nothing
    about K-scheme's storage changed. I-scheme has no meaningful
    "abs_row/abs_col" (variable rows per subject), so it writes straight
    to `canonical_rows` instead. Callers should save both.

    Separately, for ANY semester that's been trained through the newer
    subject/level/component tree trainer (Train mode Steps 1-6 -- i.e. it
    has rows in the `subjects` table), this ALSO plays that trained
    template back against the same chunk via extract_subjectwise_from_chunk()
    and appends the result to `subjectwise_records`. This runs independently
    of the scheme_id/flat-mapping check above -- the flat mapping for such
    a semester only needs to cover the identity/summary fields (Name,
    Enrollment No, Total Marks, Result, etc.); subject-wise marks come
    entirely from the tree trainer now. Callers should save this via
    save_subjectwise_student_records_to_db()."""
    extracted = []
    canonical_rows = []
    subjectwise_records = []
    review = []

    subjectwise_semesters = set(list_subjectwise_semesters(db_path))

    soup = BeautifulSoup(html, "html.parser")
    tables = soup.find_all("table")
    chunks = group_tables(tables)

    if not chunks:
        review.append({"enrollment": enrollment, "semester_label": None,
                        "reason": "No result tables found (wrong enrollment or no result available)."})
        return extracted, canonical_rows, subjectwise_records, review

    for group_idx, chunk in enumerate(chunks):
        header_grid = expand_table_grid(chunk[0])
        label = extract_semester_label(header_grid)

        if not label:
            review.append({"enrollment": enrollment, "semester_label": None,
                            "reason": f"Could not detect a semester label for table group {group_idx}."})
            continue

        if label in subjectwise_semesters:
            if is_vertical_semester(label, db_path):
                subj_records, subj_review = extract_subjectwise_vertical_from_chunk(chunk, label, enrollment, db_path)
            else:
                subj_records, subj_review = extract_subjectwise_from_chunk(chunk, label, enrollment, db_path)
            subjectwise_records.extend(subj_records)
            review.extend(subj_review)

        scheme_id = detect_scheme_in_chunk(chunk)
        if scheme_id is None:
            # Structural signature detection only knows the two legacy
            # header layouts (SCHEME_SIGNATURES) -- a different institute's
            # sheet (e.g. TH/PR/PA/ESE headers instead of FA-TH/SA-TH or
            # COURSE HEAD) will never match either one, even though the
            # flat trainer's ranges for this semester are just as usable
            # regardless of header wording. Fall back to whichever scheme
            # namespace already has a trained mapping for this label --
            # that alone tells us which extractor applies.
            for candidate in ("k_scheme", "i_scheme"):
                if label in mapping.get(candidate, {}):
                    scheme_id = candidate
                    break
        if scheme_id is None:
            if label not in subjectwise_semesters:
                review.append({"enrollment": enrollment, "semester_label": label,
                                "reason": "Could not detect a known scheme (layout) for this semester's "
                                          "tables, and no trained identity/summary mapping exists for it "
                                          "either. This may be a new MSBTE layout -- check SCHEME_SIGNATURES, "
                                          "or run Train mode's flat range-selector step for this semester."})
            continue

        scheme_mapping = mapping.get(scheme_id, {})
        if label not in scheme_mapping:
            if label not in subjectwise_semesters:
                review.append({"enrollment": enrollment, "semester_label": label,
                                "reason": f"No trained [{scheme_id}] mapping for this semester. Run 'train' mode to add it."})
            continue

        if scheme_id == "k_scheme":
            chunk_extracted, chunk_review = apply_mapping_to_chunk(chunk, label, scheme_mapping[label], enrollment)
            extracted.extend(chunk_extracted)
            review.extend(chunk_review)
        else:
            chunk_canonical, chunk_review = apply_i_scheme_mapping_to_chunk(chunk, label, scheme_mapping[label], enrollment)
            canonical_rows.extend(chunk_canonical)
            review.extend(chunk_review)

    return extracted, canonical_rows, subjectwise_records, review


# ==========================================================
# PIVOT TO WIDE FORMAT
# One row per (enrollment, semester_label). Each extracted record is
# already ONE atomic cell (field_name already encodes category/row/col,
# e.g. "subjects_r3_c7") so records can be grouped/reshaped however a
# given report needs -- no delimiter splitting needed.
# ==========================================================

def is_dash(value):
    """True if value is a lone '-' (MSBTE's 'not applicable' placeholder,
    e.g. a subject with no Practical shows '-' for its PR marks) -- as
    opposed to a real blank or a real numeric/AB value."""
    return value is not None and str(value).strip() == "-"


def clean_value(value):
    """Turn a lone '-' into a real blank. Applied to every cell written
    out, as a safety net beyond the column-level exclusion below."""
    return "" if is_dash(value) else value


def parse_exam_session(raw_text):
    """Parse a semester's raw "Year" field (trained/extracted the same
    per-student way as Program/Name -- see GROUPS -- e.g. "SUMMER-2026",
    "WINTER - 2025", "2026 SUMMER") into (session, year, academic_year,
    exam_label):
        session       -- "SUMMER" or "WINTER" (None if not recognized)
        year          -- the 4-digit exam year as an int (None if not found)
        academic_year -- MSBTE writes this differently depending on
                          session: Summer's academic year is written out
                          in full ("SUMMER-2026" -> "2025-2026"), Winter's
                          abbreviates the second year ("WINTER-2025" ->
                          "2025-26") -- both per how MSBTE itself labels
                          these on official documents
        exam_label    -- nicely cased, e.g. "Summer 2026" / "Winter 2025"
    Returns all None/"" if raw_text doesn't contain a recognizable
    session + year (e.g. this semester was trained before Year existed).
    """
    if not raw_text:
        return None, None, "", ""
    text = str(raw_text).upper()
    m = re.search(r"(19|20)\d{2}", text)
    year = int(m.group(0)) if m else None
    if "SUMM" in text:
        session = "SUMMER"
    elif "WINT" in text:
        session = "WINTER"
    else:
        session = None
    if session and not year:
        # No 4-digit year found (e.g. someone typed "Summer 26" rather
        # than "Summer 2026" during Offline Import) -- fall back to a
        # standalone 2-digit number and assume the 2000s, rather than
        # dropping the whole Academic Year line from the report header.
        m2 = re.search(r"\b(\d{2})\b", text)
        if m2:
            year = 2000 + int(m2.group(1))
    if not session or not year:
        return session, year, "", ""
    academic_year = f"{year - 1}-{year}" if session == "SUMMER" else f"{year}-{str(year + 1)[-2:]}"
    return session, year, academic_year, f"{session.title()} {year}"


def get_semester_identity_text(semester_label, group_name, db_path=DB_FILE):
    """The raw text of an identity-like field (e.g. "year", "program")
    for one semester as a whole -- these are trained/extracted per
    student, but the value is the same for every student in a semester's
    batch, so this just returns whichever non-blank one turns up first.
    Used for report headings, where one representative value per
    semester is wanted rather than a per-student column.

    '' if nothing was ever trained/extracted for this group in this
    semester (e.g. an older mapping trained before Year existed).
    """
    all_extracted, _ = load_all_records_from_db(db_path)
    for r in all_extracted:
        if (r["semester_label"] == semester_label and r["group_name"] == group_name
                and r["enrollment"] and r["value"]):
            val = clean_value(r["value"])
            if val:
                return val
    return ""


def compute_percentage_fallback(total_marks_text, obtained_marks_text):
    """If a semester's Percentage value is missing/blank but its Total
    Marks and Obtained Total Marks are both present and numeric, compute
    Percentage = Obtained / Total * 100 rather than leaving it blank.

    Used by BOTH reports: the semester-wise report's Percentage column,
    and the Yearly Result report (whose Percentage column AND year-average-marks
    calculation would otherwise be thrown off by treating a missing
    percentage as if that semester never happened, when the marks data
    to compute it from was sitting right there).

    Returns a "94.32"-style string, or None if total/obtained aren't both
    present and numeric (nothing to safely compute from).
    """
    try:
        total = float(str(total_marks_text).strip())
        obtained = float(str(obtained_marks_text).strip())
    except (TypeError, ValueError):
        return None
    if total == 0:
        return None
    return f"{(obtained / total * 100):.2f}"


def build_semester_structure(sem_records):
    """Given ALL extracted records (heading + data groups) for one semester,
    work out the fixed 'shape' of that semester's mark sheet:
      - one subject-block of columns per subject, tiled left to right
        (subject count comes straight from the 'subjects' heading group)
      - within each subject's block, one column per obtained_marks column
        (e.g. 6 exam-head columns: TH/PR/SLA x FA/SA) -- EXCEPT a column is
        dropped entirely for a subject if any obtained_marks value there is
        '-' (not applicable for that subject), so neither the heading nor
        any data cell for it appears at all, rather than showing a dash.
      - THPRSLA/FASA text for a column is looked up directly at that same
        abs_col (they span the full column range, so this always resolves)
      - maximum_marks lives in its own separate columns (e.g. 1,3,5,7,9,11
        vs obtained_marks' 2,4,6,8,10,12), so its column is paired to the
        matching obtained_marks column by rank (1st Max col <-> 1st Obt
        col, etc.) rather than by range_idx, so a training-time split
        range can't scramble the pairing.
    abs_row/abs_col are the true physical grid position, stable no matter
    how many ranges a group got split into during training.
    """
    thprsla_by_col, fasa_by_col, subject_by_row = {}, {}, {}
    maxmarks_by_cell = {}
    max_cols_seen, obt_cols_seen = set(), set()
    dash_cells = set()  # (subject_row, obt_col) pairs where any student's value was '-'

    for rec in sem_records:
        g = rec["group_name"]
        if g == "thprsla":
            thprsla_by_col.setdefault(rec["abs_col"], rec["value"])
        elif g == "fasa":
            fasa_by_col.setdefault(rec["abs_col"], rec["value"])
        elif g == "subjects":
            subject_by_row.setdefault(rec["abs_row"], rec["value"])
        elif g == "maximum_marks":
            maxmarks_by_cell.setdefault((rec["abs_row"], rec["abs_col"]), rec["value"])
            max_cols_seen.add(rec["abs_col"])
        elif g == "obtained_marks":
            obt_cols_seen.add(rec["abs_col"])
            if is_dash(rec["value"]):
                dash_cells.add((rec["abs_row"], rec["abs_col"]))

    subject_rows = sorted(subject_by_row.keys())
    obt_cols = sorted(obt_cols_seen)
    max_cols = sorted(max_cols_seen)
    max_col_for_obt_col = dict(zip(obt_cols, max_cols))  # rank-paired

    columns = [
        {"subject_row": srow, "obt_col": ocol, "max_col": max_col_for_obt_col.get(ocol)}
        for srow in subject_rows
        for ocol in obt_cols
        if (srow, ocol) not in dash_cells
    ]

    # identity_fields: one field list PER identity group
    # (name/enrollment_number/seat_number/semester) -- these are the
    # separate pieces of a student's identity line, each rendered as its
    # own labeled block. summary_fields: same idea, but for the summary
    # line (total_marks/obtained_total_marks/percentage/result).
    identity_fields = {g: [] for g in IDENTITY_GROUPS}
    summary_fields = {g: [] for g in SUMMARY_GROUPS}
    for rec in sem_records:
        gname = rec["group_name"]
        if gname in identity_fields and rec["field_name"] not in identity_fields[gname]:
            identity_fields[gname].append(rec["field_name"])
        elif gname in summary_fields and rec["field_name"] not in summary_fields[gname]:
            summary_fields[gname].append(rec["field_name"])

    return {
        "columns": columns,
        "subject_by_row": subject_by_row,
        "thprsla_by_col": thprsla_by_col,
        "fasa_by_col": fasa_by_col,
        "maxmarks_by_cell": maxmarks_by_cell,
        "identity_fields": identity_fields,
        "summary_fields": summary_fields,
    }


def build_semester_structure_subjectwise(semester_label, db_path=DB_FILE):
    """Same purpose as build_semester_structure() above, but for a
    semester trained via the newer subject/level/component TREE trainer
    (Train mode Steps 1-6: select subjects -> choose levels -> build
    template -> review checkboxes -> fill values) instead of the old flat
    TH/PR/SLA + FA/SA ranges.

    The tree trainer supports 1-3 arbitrary levels (semester_template_settings.
    max_levels), so column headers here are N rows deep -- one row per
    level, however deep THIS semester's tree actually goes -- rather than
    the old fixed 2 rows (TH/PR/SLA, then FA/SA). A leaf shallower than
    max_levels (a branch that ends early) gets blank cells for its unused
    deeper levels, each keyed uniquely so they never accidentally merge
    with a neighboring column's blank cells.

    Marks come from subjectwise_student_records (role='obtained' for data
    rows, role='max' for the header's Max Marks row) -- NOT
    student_records/semester_headings, which only hold this semester's
    identity/summary fields once a semester has moved to this trainer.
    """
    subjects = load_subjects(semester_label, db_path)
    nodes = load_component_template(semester_label, db_path)
    nodes_by_id = {n["node_id"]: n for n in nodes}
    disabled_set = load_subject_node_disabled(semester_label, db_path)
    leaves = leaf_nodes(nodes)
    max_levels = load_component_template_settings(semester_label, db_path) or max(
        (n["level"] for n in nodes), default=1
    )

    conn = sqlite3.connect(db_path)
    conn.row_factory = sqlite3.Row
    rows = conn.execute(
        "SELECT * FROM subjectwise_student_records WHERE semester_label = ?", (semester_label,)
    ).fetchall()
    conn.close()

    obtained_by_enr_col = {}
    max_by_col = {}
    values_by_col = {}
    for r in rows:
        col_key = (r["subject_index"], r["node_id"])
        if r["role"] == "obtained":
            obtained_by_enr_col.setdefault(r["enrollment"], {})[col_key] = r["value"]
            values_by_col.setdefault(col_key, []).append(r["value"])
        elif r["role"] == "max":
            max_by_col.setdefault(col_key, r["value"])

    def is_blank_or_dash(value):
        return value is None or str(value).strip() in ("", "-")

    # A (subject, leaf) column is dropped entirely -- header AND data --
    # if every recorded value for it, across every enrollment, is blank/
    # dash/missing (e.g. a subject that never actually has a Practicals
    # component, so MSBTE shows nothing there for anyone). A column with
    # even one real mark anywhere is kept, so one absent student's blank
    # cell doesn't wipe the column out for everyone else.
    blank_cols = {
        col_key for col_key, vals in values_by_col.items()
        if all(is_blank_or_dash(v) for v in vals)
    }

    def ancestor_chain(node_id):
        chain = []
        n = nodes_by_id.get(node_id)
        while n is not None:
            chain.append(n)
            n = nodes_by_id.get(n["parent_id"]) if n["parent_id"] is not None else None
        chain.reverse()
        return chain

    columns = []
    for subj in sorted(subjects, key=lambda s: s["subject_index"]):
        for leaf in leaves:
            if not node_enabled_for_subject(leaf["node_id"], subj["subject_index"], nodes_by_id, disabled_set):
                continue
            col_key = (subj["subject_index"], leaf["node_id"])
            # Drop a column with no marks at all recorded for it (never
            # extracted, or extracted but blank/dash for every student)
            # the same way blank_cols above does.
            if col_key not in values_by_col or col_key in blank_cols:
                continue
            chain = ancestor_chain(leaf["node_id"])
            level_keys = [(subj["subject_index"], n["node_id"]) for n in chain]
            level_labels = [n["label"] for n in chain]
            # Pad a branch that ends before max_levels so every column has
            # the same number of header rows below Subject.
            pad_i = 0
            while len(level_labels) < max_levels:
                level_keys.append((subj["subject_index"], leaf["node_id"], "pad", pad_i))
                level_labels.append("")
                pad_i += 1
            columns.append({
                "col_key": col_key,
                "subject_key": subj["subject_index"],
                "subject_label": subj["subject_name"],
                "level_keys": level_keys,
                "level_labels": level_labels,
                "max_label": max_by_col.get(col_key, ""),
            })

    return {
        "columns": columns,
        "max_levels": max_levels,
        "obtained_by_enr_col": obtained_by_enr_col,
    }


def count_failed_subjects(sem_records, enrollment):
    """Count how many DISTINCT subjects a student failed in one semester.

    MSBTE marks a failed subject with an asterisk in the obtained_marks
    cell (e.g. "22*", "AB*"), possibly on more than one exam-head column
    for the same subject. This counts by subject (abs_row), not by column,
    so a subject with two starred columns (e.g. both TH and PR) still
    counts as ONE failed subject.

    Works entirely off group_name/abs_row/value -- no cell addresses --
    so this same logic would work unchanged against a DB query returning
    the equivalent rows (WHERE group_name='obtained_marks' AND value LIKE '%*%').
    """
    failed_subject_rows = set()
    for rec in sem_records:
        if (rec["group_name"] == "obtained_marks"
                and rec["enrollment"] == enrollment
                and rec["value"] is not None
                and "*" in str(rec["value"])):
            failed_subject_rows.add(rec["abs_row"])
    return len(failed_subject_rows)


def parse_marks_marker(value):
    """Classify one obtained_marks cell for K7(Part A)-style statistics.
    MSBTE suffixes a raw mark with a marker character that changes what it
    means for reporting purposes:
        '#'  -- excluded from these stats entirely (e.g. "23#")
        '*'  -- a fail marker (e.g. "12*", "AB*") -- still counts as
                "appeared", just not as a pass, and IS counted as failed
        '@'  -- a grace/condoned mark -- treated as a normal numeric pass
                (e.g. "10@" counts the same as a plain "10")
        'AB' (no '*') -- unusual, but treated like any other non-numeric,
                non-hash value: appeared, not a pass, not a numeric mark
        blank / '-' / None -- not applicable / no result -- excluded
                entirely, same as '#'

    Returns a dict:
        blank      -- True if this cell shouldn't be counted at all
        hashed     -- True if the value carried a '#' (also excluded entirely)
        starred    -- True if the value carried a '*' (a fail)
        numeric    -- the plain numeric mark (float), stripping any '@'/'*'/'#'
                      suffix, or None if nothing numeric could be read
                      (e.g. a lone "AB")
    """
    if value is None:
        return {"blank": True, "hashed": False, "starred": False, "numeric": None}
    text = str(value).strip()
    if text == "" or text == "-":
        return {"blank": True, "hashed": False, "starred": False, "numeric": None}

    hashed = "#" in text
    starred = "*" in text
    m = re.search(r"\d+(\.\d+)?", text)
    numeric = float(m.group(0)) if m else None
    return {"blank": False, "hashed": hashed, "starred": starred, "numeric": numeric}


def compute_result_summary_rows(semester_label, db_path=DB_FILE, student_status="both"):
    """The small Result-summary table shown before K7 (Part B)'s main
    table: for one semester, how many enrollments (filtered by
    student_status) got each distinct Result value -- reusing the exact
    same Result text build_student_history() already extracts per
    (enrollment, semester), i.e. whatever MSBTE's own site says (e.g.
    "FIRST CLASS", "SECOND CLASS", "SECOND CLASS WITH CONDONATION",
    "FAIL") rather than anything recomputed here.

    An enrollment with no Result recorded for this semester isn't counted
    toward any bucket (it simply doesn't have a determined Result yet).

    Returns a list of (result_text, count) tuples, sorted by count
    descending (most common first), alphabetically for ties.
    """
    all_extracted, all_review = load_all_records_from_db(db_path)
    enrollments, programs_by_enr, names_by_enr, semesters, history = build_student_history(all_extracted, db_path)
    if semester_label not in semesters:
        return []

    status_map = compute_student_status(all_extracted, db_path)
    wanted = {"regular": "Regular", "ex": "EX"}.get(student_status)

    counts = {}
    for enr in enrollments:
        if wanted is not None and status_map.get((enr, semester_label)) != wanted:
            continue
        rec = history.get((enr, semester_label))
        if not rec or not rec["result"]:
            continue
        counts[rec["result"]] = counts.get(rec["result"], 0) + 1

    return sorted(counts.items(), key=lambda kv: (-kv[1], kv[0]))


def compute_k7_partb_rows(semester_label, db_path=DB_FILE, student_status="both"):
    """Build the row data for the K7 (Part B) report, ONE row per
    (subject, obtained_marks column) -- i.e. exactly the same granularity
    as build_semester_structure()'s "columns" list, since each such column
    already carries its own THPRSLA label (Theory/Practicals/SLA) and FASA
    label (FA-TH/SA-TH/TOTAL/FA-PR/SA-PR/SLA) -- there's no separate
    nesting needed for "for each subject / for each THPRSLA group / for
    each FASA group", that nesting IS the columns list.

    student_status: "regular", "ex", or "both" -- same
    compute_student_status() filtering as the other reports, applied to
    which enrollments are counted as "appeared" at all.

    Per-column stats, computed from parse_marks_marker() on every counted
    enrollment's obtained_marks value in that column:
      - lowest / highest: plain numeric marks only (a '#' or '*' value is
        excluded even if it has a number attached; a '@' value counts)
      - appeared: every non-blank, non-hashed value (numeric, '*', '@', or
        bare 'AB' all count as "appeared" -- only '#' and blank/'-' don't)
      - pass: only a fully plain numeric value (no '#'/'*'/'@' at all)
      - failed: any value carrying '*' (numeric-with-star or "AB*")
      - above 60%: plain numeric marks (same population as lowest/highest)
        whose value is more than 60% of that column's Maximum Marks
      - both percentages are computed against "appeared" as the
        denominator, matching the pass%/failed% formulas given

    Returns a list of dicts, one per column, in subject/column tiling
    order: {subject_name, course_code, thprsla, fasa, faculty_name,
    lowest, highest, appeared, pass_count, pass_pct, above60_count,
    above60_pct, fail_count, fail_pct}, plus the resolved "programme"
    string (same for every row, so returned once alongside, not repeated
    per dict) as (programme, rows).
    """
    all_extracted, all_review = load_all_records_from_db(db_path)
    sem_records = [r for r in all_extracted if r["semester_label"] == semester_label]
    if not sem_records:
        return "", []

    status_map = compute_student_status(all_extracted, db_path)

    program_by_enr = {}
    for rec in sem_records:
        if rec["group_name"] == "program" and rec["value"]:
            program_by_enr[rec["enrollment"]] = rec["value"]

    enrollments = sorted({r["enrollment"] for r in sem_records if r["enrollment"]})
    if student_status in ("regular", "ex"):
        wanted = "Regular" if student_status == "regular" else "EX"
        enrollments = [enr for enr in enrollments if status_map.get((enr, semester_label)) == wanted]

    programme = next(iter(program_by_enr.values()), "")

    is_subjectwise = semester_label in list_subjectwise_semesters(db_path)

    def stats_for(numeric_and_marker_values, max_marks):
        """values: list of raw obtained-mark strings for one column, for
        the enrollments being counted. Same rules as the docstring above."""
        numeric_pool = []
        appeared = pass_count = fail_count = above60 = 0
        for raw in numeric_and_marker_values:
            parsed = parse_marks_marker(raw)
            if parsed["blank"] or parsed["hashed"]:
                continue
            appeared += 1
            if parsed["starred"]:
                fail_count += 1
                continue
            if parsed["numeric"] is not None:
                numeric_pool.append(parsed["numeric"])
                pass_count += 1
                if max_marks and parsed["numeric"] > 0.6 * max_marks:
                    above60 += 1
        return {
            "lowest": min(numeric_pool) if numeric_pool else "",
            "highest": max(numeric_pool) if numeric_pool else "",
            "appeared": appeared,
            "pass_count": pass_count,
            "pass_pct": (pass_count / appeared * 100) if appeared else 0,
            "above60_count": above60,
            "above60_pct": (above60 / appeared * 100) if appeared else 0,
            "fail_count": fail_count,
            "fail_pct": (fail_count / appeared * 100) if appeared else 0,
        }

    rows = []
    if is_subjectwise:
        structure = build_semester_structure_subjectwise(semester_label, db_path)
        columns = structure["columns"]  # blank/dropped columns already excluded
        obtained_by_enr_col = structure["obtained_by_enr_col"]
        component_faculty_v2 = load_subject_component_faculty_v2(db_path)
        course_codes_v2 = load_subject_course_codes_v2(db_path)

        for c in columns:
            subject_index = c["subject_key"]
            # Level-1 ancestor's node_id/label = the old THPRSLA slot;
            # this leaf's own label = the old FASA slot.
            level1_node_id = c["level_keys"][0][1] if c["level_keys"] and len(c["level_keys"][0]) == 2 else None
            thprsla = c["level_labels"][0] if c["level_labels"] else ""
            fasa = c["level_labels"][-1] if len(c["level_labels"]) > 1 else ""
            faculty = component_faculty_v2.get((semester_label, subject_index, level1_node_id), "") if level1_node_id is not None else ""
            course_code = (course_codes_v2.get((semester_label, subject_index), {}) or {}).get("course_code", "")

            max_marks = parse_marks_marker(c["max_label"])["numeric"]
            raw_values = [obtained_by_enr_col.get(enr, {}).get(c["col_key"]) for enr in enrollments]
            stats = stats_for(raw_values, max_marks)
            rows.append({
                "subject_name": c["subject_label"],
                "course_code": course_code,
                "thprsla": thprsla,
                "fasa": fasa,
                "faculty_name": faculty,
                **stats,
            })
    else:
        structure = build_semester_structure(sem_records)
        columns = structure["columns"]

        obtained_by_enr_cell = {}
        for rec in sem_records:
            if rec["group_name"] == "obtained_marks":
                obtained_by_enr_cell.setdefault(rec["enrollment"], {})[(rec["abs_row"], rec["abs_col"])] = rec["value"]

        component_faculty = load_subject_component_faculty(db_path)
        course_codes = load_subject_course_codes(db_path)

        for c in columns:
            subject_row, obt_col, max_col = c["subject_row"], c["obt_col"], c["max_col"]
            subject_name = structure["subject_by_row"].get(subject_row, "")
            thprsla = structure["thprsla_by_col"].get(obt_col, "")
            fasa = structure["fasa_by_col"].get(obt_col, "")
            faculty = component_faculty.get((semester_label, subject_row, thprsla), "")
            course_code = (course_codes.get((semester_label, subject_row), {}) or {}).get("course_code", "")

            max_marks_raw = structure["maxmarks_by_cell"].get((subject_row, max_col)) if max_col is not None else None
            max_marks = parse_marks_marker(max_marks_raw)["numeric"]

            raw_values = [obtained_by_enr_cell.get(enr, {}).get((subject_row, obt_col)) for enr in enrollments]
            stats = stats_for(raw_values, max_marks)
            rows.append({
                "subject_name": subject_name,
                "course_code": course_code,
                "thprsla": thprsla,
                "fasa": fasa,
                "faculty_name": faculty,
                **stats,
            })

    return programme, rows


def generate_k7_partb_pdf(db_path=DB_FILE, out_path=None, student_status="both",
                           semesters=None, fail_pct_threshold=30.0):
    """Build the K7 (Part B) report as one print-ready landscape A4 PDF,
    with one section per semester (each with its own Sr.No. numbering --
    ONE number per subject, not per table row, merged/spanned across
    that subject's own THPRSLA-component/FASA-column rows the same way
    the Subject column itself is -- so Sr.No. counts how many subjects
    are in the semester, its own copy of K7 (Part B)'s fixed masthead
    heading -- see build_k7b_heading_flowables() -- and its own
    signature block at the end -- see build_report_end_flowables()) --
    one row per subject/THPRSLA-component/FASA-column, across every
    enrollment matching student_status (see compute_k7_partb_rows()).

    semesters: which semester labels to include, in order (defaults to
    every semester found in the database, in SEMESTER_NAMES order). A
    semester with no rows at all, or where every row's "appeared" count
    is 0 (nothing but zeroes throughout), is skipped entirely rather than
    printed as an empty/all-zero table.

    Each semester starts on its own fresh page. Within a semester, a
    Failed % cell is highlighted (orange background) whenever it exceeds
    fail_pct_threshold, so the trouble spots jump out. Repeated
    Programme/Faculty Name/Course Code/Subject/THPRSLA/FASA values down a
    column are shown once and visually merged (vertical span) rather than
    repeated on every row -- blank Faculty Name/Course Code cells are
    left unmerged so an empty block doesn't visually bridge unrelated
    subjects. The Programme column (one merged cell spanning the whole
    table) is drawn as vertical text reading bottom-to-top, centered in
    its column.
    """
    from reportlab.lib.pagesizes import A4, landscape
    from reportlab.platypus import SimpleDocTemplate, Table, TableStyle, Paragraph, Spacer, PageBreak, Flowable
    from reportlab.lib.styles import getSampleStyleSheet
    from reportlab.lib.enums import TA_CENTER, TA_LEFT
    from reportlab.lib import colors
    from reportlab.lib.units import mm
    from reportlab.pdfbase.pdfmetrics import stringWidth

    class VerticalText(Flowable):
        """Draws `text` rotated 90 degrees so it reads bottom-to-top
        (used for the Programme column, which is one merged cell running
        the full height of the table). Sized to the text's own natural
        rotated footprint -- small width, height = the text's length --
        so the table's normal centered alignment centers it within the
        actual (much larger) merged cell around it.
        """
        def __init__(self, text, font_name="Helvetica-Bold", font_size=9):
            Flowable.__init__(self)
            self.text = text
            self.font_name = font_name
            self.font_size = font_size
            self._text_len = stringWidth(text, font_name, font_size)

        def wrap(self, availWidth, availHeight):
            return (self.font_size + 3, min(self._text_len, availHeight))

        def draw(self):
            c = self.canv
            c.saveState()
            c.setFont(self.font_name, self.font_size)
            c.rotate(90)
            c.drawString(1, -self.font_size + 1, self.text)
            c.restoreState()

    if semesters is None:
        all_extracted, _ = load_all_records_from_db(db_path)
        semesters = sorted({r["semester_label"] for r in all_extracted if r["enrollment"]},
                            key=lambda s: SEMESTER_NAMES.index(s) if s in SEMESTER_NAMES else 999)

    styles = getSampleStyleSheet()
    font_size = 7
    cell_style = styles["Normal"].clone("k7cell")
    cell_style.fontSize = font_size
    cell_style.leading = font_size + 1
    cell_style.alignment = TA_CENTER
    left_cell_style = cell_style.clone("k7cellleft")
    left_cell_style.alignment = TA_LEFT
    header_style = cell_style.clone("k7hdr")
    header_style.fontName = "Helvetica-Bold"
    header_style.alignment = TA_CENTER

    def P(text, style=cell_style):
        return Paragraph(str(text) if text not in (None, "") else "&nbsp;", style)

    def fmt_num(n):
        return "" if n == "" else (str(int(n)) if float(n).is_integer() else f"{n:.2f}")

    def fmt_pct(n):
        return f"{n:.2f}"

    def merge_runs(style_cmds, values, col_idx, row_offset=1):
        """Add a SPAN for every run of 2+ consecutive equal values in
        `values`, in column col_idx, starting at table row row_offset
        (row 0 is the header). Only the first row of a run keeps its
        text visible; reportlab simply doesn't draw the covered cells.
        """
        run_start = 0
        n = len(values)
        for i in range(1, n + 1):
            if i == n or values[i] != values[run_start]:
                if i - run_start > 1:
                    style_cmds.append(("SPAN", (col_idx, row_offset + run_start),
                                        (col_idx, row_offset + i - 1)))
                run_start = i

    COLUMNS = [
        ("Sr.No.", 8), ("Programme", 32), ("Faculty Name", 26), ("Course Code", 16), ("Subject", 40),
        ("THPRSLA", 16), ("FASA", 14), ("Lowest", 11), ("Highest", 11),
        ("Appeared", 13), ("Pass", 10), ("Pass %", 11), ("Above 60%", 13),
        ("Above 60% %", 13), ("Failed", 10), ("Failed %", 11),
    ]
    FAILED_PCT_COL = 15
    page_w_mm, margin_mm = 297, 4
    usable_w_mm = page_w_mm - 2 * margin_mm
    raw_widths = [w for _, w in COLUMNS]
    scale = usable_w_mm / sum(raw_widths)
    col_widths = [w * scale * mm for w in raw_widths]

    out_path = out_path or "K7_PartB_Report.pdf"
    doc = SimpleDocTemplate(out_path, pagesize=landscape(A4),
                             leftMargin=margin_mm * mm, rightMargin=margin_mm * mm,
                             topMargin=margin_mm * mm, bottomMargin=margin_mm * mm)
    story = []
    included_semesters = []

    for sem_label in semesters:
        programme, rows = compute_k7_partb_rows(sem_label, db_path, student_status)
        if not rows or sum(r["appeared"] for r in rows) == 0:
            print(f"  Skipping {sem_label.title()} -- no data (or nothing but zeroes) for K7 (Part B).")
            continue

        if included_semesters:
            story.append(PageBreak())  # every semester starts on its own fresh page
        included_semesters.append(sem_label)

        story.extend(build_k7b_heading_flowables(sem_label, db_path))
        status_note = {"regular": " (Regular)", "ex": " (EX)", "both": ""}.get(student_status, "")
        story.append(Paragraph(f"{sem_label.title()}{status_note}", styles["Heading3"]))
        story.append(Spacer(1, 3))
        gap_style = styles["Normal"].clone("k7bgap")
        gap_style.fontSize = 8
        gap_warn_style = gap_style.clone("k7bgapwarn")
        gap_warn_style.textColor = colors.HexColor("#B30000")
        for i, line in enumerate(_report_seating_gap_lines(sem_label, student_status, db_path)):
            story.append(Paragraph(line, gap_warn_style if i > 0 else gap_style))
        story.append(Spacer(1, 3))

        header = [P(label, header_style) for label, _ in COLUMNS]
        table_data = [header]
        style_cmds = [
            ("GRID", (0, 0), (-1, -1), 0.3, colors.grey),
            ("BACKGROUND", (0, 0), (-1, 0), colors.HexColor("#4472C4")),
            ("TEXTCOLOR", (0, 0), (-1, 0), colors.white),
            ("VALIGN", (0, 0), (-1, -1), "MIDDLE"),
            ("LEFTPADDING", (0, 0), (-1, -1), 2),
            ("RIGHTPADDING", (0, 0), (-1, -1), 2),
            ("TOPPADDING", (0, 0), (-1, -1), 1.5),
            ("BOTTOMPADDING", (0, 0), (-1, -1), 1.5),
            ("ALIGN", (1, 1), (1, -1), "CENTER"),  # centers the rotated Programme text in its column
        ]
        # Sr.No. counts SUBJECTS, not table rows -- it increments once
        # per subject (a run of consecutive rows sharing the same
        # Subject), matching how many subjects are in this semester,
        # not how many THPRSLA/FASA rows they expand into. Table-row
        # addressing (for SPAN/BACKGROUND) still uses the physical row
        # position, tracked separately as row_idx.
        subject_names = [r["subject_name"] for r in rows]
        subject_sr_no_for_row = []
        _counter, _prev = 0, object()  # sentinel -- never equals a real subject name
        for name in subject_names:
            if name != _prev:
                _counter += 1
                _prev = name
            subject_sr_no_for_row.append(_counter)

        for row_idx, row in enumerate(rows, start=1):
            subject_sr_no = subject_sr_no_for_row[row_idx - 1]
            table_data.append([
                P(subject_sr_no),
                VerticalText(programme) if row_idx == 1 and programme else P("", left_cell_style),
                P(row["faculty_name"], left_cell_style),
                P(row["course_code"], left_cell_style),
                P(row["subject_name"], left_cell_style),
                P(row["thprsla"]),
                P(row["fasa"]),
                P(fmt_num(row["lowest"])),
                P(fmt_num(row["highest"])),
                P(row["appeared"]),
                P(row["pass_count"]),
                P(fmt_pct(row["pass_pct"])),
                P(row["above60_count"]),
                P(fmt_pct(row["above60_pct"])),
                P(row["fail_count"]),
                P(fmt_pct(row["fail_pct"])),
            ])
            if row["fail_pct"] > fail_pct_threshold:
                style_cmds.append(("BACKGROUND", (FAILED_PCT_COL, row_idx), (FAILED_PCT_COL, row_idx),
                                    colors.HexColor("#FFA500")))

        # Collapse repeated Sr.No./Programme/Subject/THPRSLA/FASA
        # values down the column into one merged (spanned) cell instead
        # of repeating them. Sr.No. and Subject always change together
        # (that's the whole point -- one Sr.No. per subject), so the
        # same subject_names run boundaries merge both.
        merge_runs(style_cmds, subject_names, 0)
        merge_runs(style_cmds, [programme] * len(rows), 1)
        # Blank faculty cells are made unique per row first so they don't
        # merge into one giant empty block spanning unrelated subjects --
        # only an ACTUAL repeated faculty name gets merged.
        faculty_values = [r["faculty_name"] if r["faculty_name"] else f"__blank_{i}__"
                           for i, r in enumerate(rows)]
        merge_runs(style_cmds, faculty_values, 2)
        # Course Code follows the same subject-boundary rule as Subject
        # itself (they always change together), so its own blank-safe
        # unique-per-row trick isn't needed -- but still skip merging
        # blanks across subjects, same reasoning as faculty.
        code_values = [r["course_code"] if r["course_code"] else f"__blank_{i}__"
                       for i, r in enumerate(rows)]
        merge_runs(style_cmds, code_values, 3)
        merge_runs(style_cmds, subject_names, 4)
        merge_runs(style_cmds, [r["thprsla"] for r in rows], 5)
        merge_runs(style_cmds, [r["fasa"] for r in rows], 6)

        t = Table(table_data, colWidths=col_widths, repeatRows=1)
        t.setStyle(TableStyle(style_cmds))
        story.append(t)
        story.extend(build_report_end_flowables())
        story.append(Spacer(1, 10))

    if not included_semesters:
        print(f"No student data found for K7 (Part B) [{student_status}] in {db_path}.")
        return None

    doc.build(story)
    print(f"Saved PDF: {out_path}  (landscape A4, K7 (Part B), [{student_status}], "
          f"{len(included_semesters)} semester section(s), Failed % highlighted above "
          f"{fail_pct_threshold}%)")
    return out_path


def save_k7c_labels(level1_label, fa_label, sa_label, db_path=DB_FILE):
    """Persist the global Level 1 / FA / SA label choice K7 (Part C) uses
    for EVERY semester -- scheme-agnostic by construction: these are just
    whatever three label strings the user picked from one reference
    semester's dropdowns, stored in report_settings (upsert) like the
    other global report settings (Institute Name, etc.)."""
    conn = sqlite3.connect(db_path)
    for key, value in (
        ("k7c_level1_label", level1_label),
        ("k7c_fa_label", fa_label),
        ("k7c_sa_label", sa_label),
    ):
        conn.execute(
            "INSERT INTO report_settings (key, value) VALUES (?, ?) "
            "ON CONFLICT(key) DO UPDATE SET value=excluded.value",
            (key, value),
        )
    conn.commit()
    conn.close()


def load_k7c_labels(db_path=DB_FILE):
    """{"level1": ..., "fa": ..., "sa": ...} -- the saved global K7 (Part C)
    label choice, or the original K-scheme defaults ("THEORY"/"FA-TH"/
    "SA-TH") if nothing has been saved yet, so existing K-scheme users
    keep working unchanged until/unless they choose to override it."""
    defaults = {"level1": "THEORY", "fa": "FA-TH", "sa": "SA-TH"}
    if not os.path.exists(db_path):
        return defaults
    conn = sqlite3.connect(db_path)
    try:
        rows = dict(conn.execute(
            "SELECT key, value FROM report_settings WHERE key IN "
            "('k7c_level1_label', 'k7c_fa_label', 'k7c_sa_label')"
        ).fetchall())
    except sqlite3.OperationalError:
        rows = {}
    conn.close()
    return {
        "level1": rows.get("k7c_level1_label") or defaults["level1"],
        "fa": rows.get("k7c_fa_label") or defaults["fa"],
        "sa": rows.get("k7c_sa_label") or defaults["sa"],
    }


def get_k7c_level_options(semester_label, db_path=DB_FILE):
    """One reference semester's own trained Level 1 labels, and -- scoped
    per Level 1 branch -- its Level 2 (leaf) labels, for populating the
    K7 (Part C) label-picker dropdowns. Level 1 = a leaf's topmost
    ancestor label; Level 2 = the leaf's own label.

    Returns (level1_options: [str], level2_by_level1: {level1_label: [str]}),
    both in first-seen order. Empty ([], {}) if this semester has no
    subject-wise tree trained at all.
    """
    nodes = load_component_template(semester_label, db_path)
    if not nodes:
        return [], {}
    nodes_by_id = {n["node_id"]: n for n in nodes}
    leaves = leaf_nodes(nodes)

    def ancestor_chain(node_id):
        chain = []
        n = nodes_by_id.get(node_id)
        while n is not None:
            chain.append(n)
            n = nodes_by_id.get(n["parent_id"]) if n["parent_id"] is not None else None
        chain.reverse()
        return chain

    level1_options = []
    level2_by_level1 = {}
    for leaf in leaves:
        chain = ancestor_chain(leaf["node_id"])
        if not chain:
            continue
        lvl1 = chain[0]["label"]
        lvl2 = chain[-1]["label"]
        if lvl1 not in level1_options:
            level1_options.append(lvl1)
        bucket = level2_by_level1.setdefault(lvl1, [])
        if lvl2 not in bucket:
            bucket.append(lvl2)
    return level1_options, level2_by_level1


def compute_k7_partc_rows(semester_label, db_path=DB_FILE, student_status="both"):
    """Build the row data for K7 (Part C): the FA-TH vs SA-TH "Score
    Index" comparison, ONE row per Theory subject that has BOTH an FA-TH
    and an SA-TH column -- a subject with no Theory component at all
    (e.g. a pure-Practical or pure-SLA subject) simply doesn't get a row.

    Score Index (a percentage), for FA-TH and SA-TH separately:
        (sum of every appeared enrollment's obtained mark in that column)
        / (appeared enrollments x that column's Maximum Marks) x 100
    -- i.e. the average score as a % of the maximum, across everyone who
    appeared. A starred/failed numeric mark (e.g. "12*") still
    contributes its actual number here (only the '*' pass/fail
    distinction is ignored) -- the point of this report is comparing
    average FA performance against average SA performance, not who
    passed. Appeared/numeric extraction uses the same parse_marks_marker()
    rules as K7 (Part B): '#' and blank/'-' excluded, '@' counts as a
    normal numeric mark.

    Difference = the absolute (mod) difference between FA-TH Score Index
    and SA-TH Score Index, in percentage points -- always >= 0, regardless
    of whether FA or SA was the higher of the two. A large Difference is
    the classic "internal marks out of step with the external exam"
    signal this report exists to catch, in either direction.

    Returns a list of dicts: {subject_name, fa_score, sa_score,
    difference} (fa_score/sa_score/difference are None if there weren't
    enough appeared/Maximum-Marks data to compute them), in subject order.
    """
    all_extracted, all_review = load_all_records_from_db(db_path)
    sem_records = [r for r in all_extracted if r["semester_label"] == semester_label]
    if not sem_records:
        return []

    status_map = compute_student_status(all_extracted, db_path)

    enrollments = sorted({r["enrollment"] for r in sem_records if r["enrollment"]})
    if student_status in ("regular", "ex"):
        wanted = "Regular" if student_status == "regular" else "EX"
        enrollments = [enr for enr in enrollments if status_map.get((enr, semester_label)) == wanted]

    def score_index(raw_values, max_marks):
        appeared = 0
        mark_sum = 0.0
        for raw in raw_values:
            parsed = parse_marks_marker(raw)
            if parsed["blank"] or parsed["hashed"]:
                continue  # same "not counted at all" rule as everywhere else
            appeared += 1
            if parsed["numeric"] is not None:
                mark_sum += parsed["numeric"]
            # else (a bare non-numeric appeared value) contributes 0 to the sum
        if not appeared or not max_marks:
            return None
        return (mark_sum / (appeared * max_marks)) * 100

    rows = []
    is_subjectwise = semester_label in list_subjectwise_semesters(db_path)
    if is_subjectwise:
        structure = build_semester_structure_subjectwise(semester_label, db_path)
        obtained_by_enr_col = structure["obtained_by_enr_col"]

        # Which leaf column is FA-TH / SA-TH for each subject -- only a
        # leaf whose level-1 ancestor matches the global Level 1 label
        # counts. Scheme-agnostic by construction: level1_label/fa_label/
        # sa_label are just whatever three label strings the user picked
        # (see save_k7c_labels()/load_k7c_labels()) -- applied identically
        # to every semester, K-scheme or otherwise. Columns that got
        # dropped entirely (blank for every student) are already absent
        # from structure["columns"], so they never produce a pair here.
        labels = load_k7c_labels(db_path)
        theory_label = (labels["level1"] or "").strip().upper()
        fa_leaf_label = (labels["fa"] or "").strip().upper()
        sa_leaf_label = (labels["sa"] or "").strip().upper()

        fa_col_by_subject, sa_col_by_subject = {}, {}
        max_by_col = {}
        subject_name_by_key = {}
        for c in structure["columns"]:
            subj = c["subject_key"]
            subject_name_by_key[subj] = c["subject_label"]
            if not c["level_labels"] or c["level_labels"][0].strip().upper() != theory_label:
                continue
            leaf_label = (c["level_labels"][-1] or "").strip().upper()
            max_by_col[c["col_key"]] = parse_marks_marker(c["max_label"])["numeric"]
            if leaf_label == fa_leaf_label:
                fa_col_by_subject[subj] = c["col_key"]
            elif leaf_label == sa_leaf_label:
                sa_col_by_subject[subj] = c["col_key"]

        for subj in sorted(subject_name_by_key):
            if subj not in fa_col_by_subject or subj not in sa_col_by_subject:
                continue  # no Theory FA-TH/SA-TH pair for this subject -- no row
            fa_col = fa_col_by_subject[subj]
            sa_col = sa_col_by_subject[subj]
            fa_values = [obtained_by_enr_col.get(enr, {}).get(fa_col) for enr in enrollments]
            sa_values = [obtained_by_enr_col.get(enr, {}).get(sa_col) for enr in enrollments]
            fa_score = score_index(fa_values, max_by_col.get(fa_col))
            sa_score = score_index(sa_values, max_by_col.get(sa_col))
            difference = abs(fa_score - sa_score) if (fa_score is not None and sa_score is not None) else None
            rows.append({
                "subject_name": subject_name_by_key[subj],
                "fa_score": fa_score,
                "sa_score": sa_score,
                "difference": difference,
            })
        return rows

    structure = build_semester_structure(sem_records)
    columns = structure["columns"]

    obtained_by_enr_cell = {}
    for rec in sem_records:
        if rec["group_name"] == "obtained_marks":
            obtained_by_enr_cell.setdefault(rec["enrollment"], {})[(rec["abs_row"], rec["abs_col"])] = rec["value"]

    # Which column is FA-TH / SA-TH for each subject (only THEORY columns
    # count -- a Practicals or SLA column never qualifies here even if
    # mislabelled FA/SA elsewhere).
    fa_col_by_subject, sa_col_by_subject, max_col_by_obt_col = {}, {}, {}
    for c in columns:
        srow, ocol, mcol = c["subject_row"], c["obt_col"], c["max_col"]
        if structure["thprsla_by_col"].get(ocol) != "THEORY":
            continue
        fasa = structure["fasa_by_col"].get(ocol, "")
        if fasa == "FA-TH":
            fa_col_by_subject[srow] = ocol
        elif fasa == "SA-TH":
            sa_col_by_subject[srow] = ocol
        max_col_by_obt_col[ocol] = mcol

    for subject_row in sorted(structure["subject_by_row"].keys()):
        if subject_row not in fa_col_by_subject or subject_row not in sa_col_by_subject:
            continue  # no Theory FA-TH/SA-TH pair for this subject -- no row
        fa_col, sa_col = fa_col_by_subject[subject_row], sa_col_by_subject[subject_row]
        fa_max = parse_marks_marker(
            structure["maxmarks_by_cell"].get((subject_row, max_col_by_obt_col.get(fa_col)))
        )["numeric"]
        sa_max = parse_marks_marker(
            structure["maxmarks_by_cell"].get((subject_row, max_col_by_obt_col.get(sa_col)))
        )["numeric"]
        fa_values = [obtained_by_enr_cell.get(enr, {}).get((subject_row, fa_col)) for enr in enrollments]
        sa_values = [obtained_by_enr_cell.get(enr, {}).get((subject_row, sa_col)) for enr in enrollments]
        fa_score = score_index(fa_values, fa_max)
        sa_score = score_index(sa_values, sa_max)
        difference = abs(fa_score - sa_score) if (fa_score is not None and sa_score is not None) else None
        rows.append({
            "subject_name": structure["subject_by_row"].get(subject_row, ""),
            "fa_score": fa_score,
            "sa_score": sa_score,
            "difference": difference,
        })
    return rows


def generate_k7_partc_pdf(db_path=DB_FILE, out_path=None, student_status="both",
                           semesters=None, diff_threshold=20.0):
    """Build the K7 (Part C) report -- the FA-TH vs SA-TH Score Index
    comparison -- as one print-ready landscape A4 PDF, one section per
    semester (each starting on its own fresh page, empty semesters
    skipped, each with its own copy of K7 (Part C)'s fixed masthead
    heading -- see build_k7c_heading_flowables() -- and its own
    signature block at the end -- see build_report_end_flowables()),
    one row per Theory subject (see compute_k7_partc_rows()).

    Columns: Sr.No. / Course Title / FA_TH Score Index / SA_TH Score
    Index / Difference / "If difference is greater than {diff_threshold}%
    Give remarks" (left blank -- for someone to fill in by hand). A
    Difference cell is highlighted (orange) whenever its magnitude
    exceeds diff_threshold, so which subjects need a remark jumps out
    without having to scan every row.
    """
    from reportlab.lib.pagesizes import A4, landscape
    from reportlab.platypus import SimpleDocTemplate, Table, TableStyle, Paragraph, Spacer, PageBreak
    from reportlab.lib.styles import getSampleStyleSheet
    from reportlab.lib.enums import TA_CENTER, TA_LEFT
    from reportlab.lib import colors
    from reportlab.lib.units import mm

    if semesters is None:
        all_extracted, _ = load_all_records_from_db(db_path)
        semesters = sorted({r["semester_label"] for r in all_extracted if r["enrollment"]},
                            key=lambda s: SEMESTER_NAMES.index(s) if s in SEMESTER_NAMES else 999)

    styles = getSampleStyleSheet()
    font_size = 8
    cell_style = styles["Normal"].clone("k7ccell")
    cell_style.fontSize = font_size
    cell_style.leading = font_size + 1
    cell_style.alignment = TA_CENTER
    left_cell_style = cell_style.clone("k7ccellleft")
    left_cell_style.alignment = TA_LEFT
    header_style = cell_style.clone("k7chdr")
    header_style.fontName = "Helvetica-Bold"
    header_style.alignment = TA_CENTER

    def P(text, style=cell_style):
        return Paragraph(str(text) if text not in (None, "") else "&nbsp;", style)

    def fmt_pct(n):
        return "" if n is None else f"{n:.2f}%"

    COLUMNS = [
        ("Sr.No.", 8), ("Course Title", 50), ("FA_TH Score Index", 22), ("SA_TH Score Index", 22),
        ("Difference", 18), (f"If difference is greater than {diff_threshold:g}% Give remarks", 40),
    ]
    DIFF_COL = 4
    page_w_mm, margin_mm = 297, 4
    usable_w_mm = page_w_mm - 2 * margin_mm
    raw_widths = [w for _, w in COLUMNS]
    scale = usable_w_mm / sum(raw_widths)
    col_widths = [w * scale * mm for w in raw_widths]

    out_path = out_path or "K7_PartC_Report.pdf"
    doc = SimpleDocTemplate(out_path, pagesize=landscape(A4),
                             leftMargin=margin_mm * mm, rightMargin=margin_mm * mm,
                             topMargin=margin_mm * mm, bottomMargin=margin_mm * mm)
    story = []
    included_semesters = []

    for sem_label in semesters:
        rows = compute_k7_partc_rows(sem_label, db_path, student_status)
        if not rows:
            print(f"  Skipping {sem_label.title()} -- no Theory subjects with both FA-TH and "
                  f"SA-TH for K7 (Part C).")
            continue

        if included_semesters:
            story.append(PageBreak())  # every semester starts on its own fresh page
        included_semesters.append(sem_label)

        story.extend(build_k7c_heading_flowables(sem_label, db_path))
        status_note = {"regular": " (Regular)", "ex": " (EX)", "both": ""}.get(student_status, "")
        story.append(Paragraph(f"{sem_label.title()}{status_note}", styles["Heading3"]))
        story.append(Spacer(1, 3))
        gap_style = styles["Normal"].clone("k7cgap")
        gap_style.fontSize = 8
        gap_warn_style = gap_style.clone("k7cgapwarn")
        gap_warn_style.textColor = colors.HexColor("#B30000")
        for i, line in enumerate(_report_seating_gap_lines(sem_label, student_status, db_path)):
            story.append(Paragraph(line, gap_warn_style if i > 0 else gap_style))
        story.append(Spacer(1, 3))

        header = [P(label, header_style) for label, _ in COLUMNS]
        table_data = [header]
        style_cmds = [
            ("GRID", (0, 0), (-1, -1), 0.3, colors.grey),
            ("BACKGROUND", (0, 0), (-1, 0), colors.HexColor("#4472C4")),
            ("TEXTCOLOR", (0, 0), (-1, 0), colors.white),
            ("VALIGN", (0, 0), (-1, -1), "MIDDLE"),
            ("LEFTPADDING", (0, 0), (-1, -1), 3),
            ("RIGHTPADDING", (0, 0), (-1, -1), 3),
            ("TOPPADDING", (0, 0), (-1, -1), 2),
            ("BOTTOMPADDING", (0, 0), (-1, -1), 2),
        ]
        for sr_no, row in enumerate(rows, start=1):
            table_data.append([
                P(sr_no),
                P(row["subject_name"], left_cell_style),
                P(fmt_pct(row["fa_score"])),
                P(fmt_pct(row["sa_score"])),
                P(fmt_pct(row["difference"])),
                P(""),  # Remarks -- always left blank for manual entry
            ])
            if row["difference"] is not None and abs(row["difference"]) > diff_threshold:
                style_cmds.append(("BACKGROUND", (DIFF_COL, sr_no), (DIFF_COL, sr_no),
                                    colors.HexColor("#FFA500")))

        t = Table(table_data, colWidths=col_widths, repeatRows=1)
        t.setStyle(TableStyle(style_cmds))
        story.append(t)
        story.extend(build_report_end_flowables())
        story.append(Spacer(1, 10))

    if not included_semesters:
        print(f"No Theory subjects with both FA-TH and SA-TH found for K7 (Part C) "
              f"[{student_status}] in {db_path}.")
        return None

    doc.build(story)
    print(f"Saved PDF: {out_path}  (landscape A4, K7 (Part C), [{student_status}], "
          f"{len(included_semesters)} semester section(s), Difference highlighted above "
          f"{diff_threshold}%)")
    return out_path


def init_seating_db(db_path=SEATING_DB_FILE):
    """Create the Seating Chart's OWN database (if it doesn't exist yet)
    and its one table. Deliberately separate from init_db()/DB_FILE --
    seating_chart data is shared across every scheme (it's what scheme
    detection itself is built from), so it can never live inside any one
    scheme's own per-scheme database. See SEATING_DB_FILE's definition
    above for the full reasoning.
    """
    conn = sqlite3.connect(db_path)
    conn.execute("""
        CREATE TABLE IF NOT EXISTS seating_chart (
            enrollment TEXT NOT NULL,
            semester_label TEXT NOT NULL,
            scheme TEXT NOT NULL,          -- e.g. 'K', 'I' -- parsed from the semester-scheme cell
            student_name TEXT,
            seat_number TEXT,
            status TEXT NOT NULL,          -- 'Regular' or 'EX', MSBTE's own answer
            subjects_appeared TEXT,        -- raw comma-separated text, not matched/used anywhere yet
            UNIQUE(enrollment, semester_label, scheme)
        )
    """)
    # Migration: a seating_chart table created before 'scheme' existed --
    # add the column (existing rows default to scheme='K', since K-scheme
    # was the only one in use before this change).
    existing_seating_cols = {row[1] for row in conn.execute("PRAGMA table_info(seating_chart)")}
    if "scheme" not in existing_seating_cols:
        conn.execute("ALTER TABLE seating_chart ADD COLUMN scheme TEXT")
        conn.execute("UPDATE seating_chart SET scheme = 'K' WHERE scheme IS NULL")
    conn.commit()
    conn.close()


def init_db(db_path=DB_FILE):
    """Create the database file (if it doesn't exist yet) and its tables.

    Two tables instead of one, to avoid storing the same facts over and
    over: subjects/THPRSLA/FASA/maximum_marks are the same for every
    student in a given semester (they're the mark-sheet's fixed structure,
    the same thing the semester-wise PDF report is built from), so
    they're saved ONCE per semester in `semester_headings`. Only what
    actually varies per student -- identity fields, obtained_marks, summary fields -- goes
    into `student_records`, once per enrollment.

    NOTE: does NOT create seating_chart -- that table lives only in
    SEATING_DB_FILE, via init_seating_db(). A per-scheme database
    created by this function has no seating_chart table at all.
    """
    conn = sqlite3.connect(db_path)
    conn.execute("""
        CREATE TABLE IF NOT EXISTS semester_headings (
            semester_label TEXT NOT NULL,
            group_name TEXT NOT NULL,
            field_name TEXT NOT NULL,
            range_idx INTEGER,
            row_offset INTEGER,
            col_offset INTEGER,
            abs_row INTEGER NOT NULL,
            abs_col INTEGER NOT NULL,
            value TEXT,
            UNIQUE(semester_label, group_name, abs_row, abs_col)
        )
    """)
    conn.execute("""
        CREATE TABLE IF NOT EXISTS student_records (
            enrollment TEXT NOT NULL,
            semester_label TEXT NOT NULL,
            group_name TEXT NOT NULL,
            field_name TEXT NOT NULL,
            range_idx INTEGER,
            row_offset INTEGER,
            col_offset INTEGER,
            abs_row INTEGER NOT NULL,
            abs_col INTEGER NOT NULL,
            value TEXT,
            UNIQUE(enrollment, semester_label, group_name, abs_row, abs_col)
        )
    """)
    conn.execute("""
        CREATE TABLE IF NOT EXISTS review_records (
            enrollment TEXT NOT NULL,
            semester_label TEXT,
            reason TEXT NOT NULL
        )
    """)
    # --- Subject-wise training v2 (scheme-agnostic, nested template tree) ---
    # Step 1: subjects (just their name-cell location, one per subject).
    conn.execute("""
        CREATE TABLE IF NOT EXISTS subjects (
            semester_label TEXT NOT NULL,
            subject_index INTEGER NOT NULL,
            subject_name TEXT NOT NULL,
            position INTEGER NOT NULL,
            abs_row INTEGER NOT NULL,
            abs_col INTEGER NOT NULL,
            UNIQUE(semester_label, subject_index)
        )
    """)
    # Step 2: how many nested levels this semester's template uses (1-4).
    conn.execute("""
        CREATE TABLE IF NOT EXISTS semester_template_settings (
            semester_label TEXT PRIMARY KEY,
            max_levels INTEGER NOT NULL
        )
    """)
    # Steps 3-5: the shared nested component tree (TH>FA>Max marks etc.),
    # defined ONCE per semester and applied to every subject.
    conn.execute("""
        CREATE TABLE IF NOT EXISTS component_template (
            semester_label TEXT NOT NULL,
            node_id INTEGER NOT NULL,
            parent_id INTEGER,
            level INTEGER NOT NULL,
            label TEXT NOT NULL,
            UNIQUE(semester_label, node_id)
        )
    """)
    # Tree-diagram checkboxes: which (subject, node) pairs are unchecked
    # for a subject that doesn't actually have that branch. Off cascades
    # to all descendants; everything not listed here is ON by default.
    conn.execute("""
        CREATE TABLE IF NOT EXISTS subject_node_disabled (
            semester_label TEXT NOT NULL,
            subject_index INTEGER NOT NULL,
            node_id INTEGER NOT NULL,
            UNIQUE(semester_label, subject_index, node_id)
        )
    """)
    # Step 6: the trained Max/Obtained cell for each (subject, leaf).
    conn.execute("""
        CREATE TABLE IF NOT EXISTS subject_node_values (
            semester_label TEXT NOT NULL,
            subject_index INTEGER NOT NULL,
            node_id INTEGER NOT NULL,
            role TEXT NOT NULL,
            position INTEGER NOT NULL,
            abs_row INTEGER NOT NULL,
            abs_col INTEGER NOT NULL,
            UNIQUE(semester_label, subject_index, node_id, role)
        )
    """)
    # The EXTRACTED per-student values, read back using the tables above
    # -- no scheme branching anywhere in how this table is populated.
    conn.execute("""
        CREATE TABLE IF NOT EXISTS subjectwise_student_records (
            enrollment TEXT NOT NULL,
            semester_label TEXT NOT NULL,
            subject_index INTEGER NOT NULL,
            subject_name TEXT NOT NULL,
            node_id INTEGER NOT NULL,
            component_label TEXT NOT NULL,
            role TEXT NOT NULL,
            value TEXT,
            UNIQUE(enrollment, semester_label, subject_index, node_id, role)
        )
    """)
    # A VERTICAL-orientation semester (I-scheme-style: one subject = a
    # variable-height block of rows, not a fixed row) can't reuse fixed
    # (abs_row, abs_col) positions the way subject_node_values does --
    # row position differs per student. Instead this stores the COLUMN
    # ROLES trained once (title/level/max/obt columns, which ARE fixed
    # across students), and every real student's rows get re-walked
    # dynamically at extraction time using these column positions --
    # see extract_subjectwise_vertical_from_chunk(). The resulting values
    # still land in subjectwise_student_records like everything else, so
    # no report code needs to know this table exists.
    conn.execute("""
        CREATE TABLE IF NOT EXISTS subjectwise_vertical_roles (
            semester_label TEXT PRIMARY KEY,
            position INTEGER NOT NULL,
            row_start INTEGER NOT NULL,
            row_end INTEGER NOT NULL,
            col_start INTEGER NOT NULL,
            col_end INTEGER NOT NULL,
            title_col INTEGER NOT NULL,
            level_cols TEXT NOT NULL,
            max_col INTEGER NOT NULL,
            obt_col INTEGER NOT NULL
        )
    """)
    # Migration: tag existing raw records as k_scheme (the only scheme
    # that existed before this column was added), so old data keeps
    # meaning "K-scheme" without a manual backfill step.
    for raw_table in ("semester_headings", "student_records"):
        cols = {row[1] for row in conn.execute(f"PRAGMA table_info({raw_table})")}
        if "scheme" not in cols:
            conn.execute(f"ALTER TABLE {raw_table} ADD COLUMN scheme TEXT")
            conn.execute(f"UPDATE {raw_table} SET scheme = 'k_scheme' WHERE scheme IS NULL")
    # Scheme-agnostic normalized marks: one row per (enrollment, semester,
    # subject, canonical component), regardless of whether the raw sheet
    # was K-scheme (columns=components) or I-scheme (rows=components) or
    # some future layout. Report/eligibility logic should read from HERE
    # so a future scheme change doesn't require touching report code --
    # only a new SCHEME_SIGNATURES entry + extractor + *_COMPONENT_MAP.
    conn.execute("""
        CREATE TABLE IF NOT EXISTS canonical_marks (
            enrollment TEXT NOT NULL,
            semester_label TEXT NOT NULL,
            scheme TEXT NOT NULL,
            subject_name TEXT NOT NULL,
            component TEXT NOT NULL,
            max_marks TEXT,
            obtained_marks TEXT,
            credits TEXT,
            UNIQUE(enrollment, semester_label, subject_name, component)
        )
    """)
    conn.execute("""
        CREATE TABLE IF NOT EXISTS subject_course_codes (
            semester_label TEXT NOT NULL,
            abs_row INTEGER NOT NULL,
            subject_name TEXT,
            abbreviation TEXT,
            course_code TEXT,
            faculty_name TEXT,
            UNIQUE(semester_label, abs_row)
        )
    """)
    # Migration: a database created before faculty_name existed still has
    # the table but without this column -- add it rather than erroring.
    existing_cols = {row[1] for row in conn.execute("PRAGMA table_info(subject_course_codes)")}
    if "faculty_name" not in existing_cols:
        conn.execute("ALTER TABLE subject_course_codes ADD COLUMN faculty_name TEXT")
    # Per-component faculty (e.g. a subject can have one faculty for THEORY
    # and a different one for PRACTICALS/SLA) -- separate table since a
    # subject can have several components, unlike the single faculty_name
    # column above (kept only for backward compatibility/migration).
    conn.execute("""
        CREATE TABLE IF NOT EXISTS subject_component_faculty (
            semester_label TEXT NOT NULL,
            abs_row INTEGER NOT NULL,
            component TEXT NOT NULL,
            faculty_name TEXT,
            UNIQUE(semester_label, abs_row, component)
        )
    """)
    # --- Course Codes v2, keyed off the subject-wise trainer's subjects/
    # component_template instead of the old flat semester_headings 'subjects'
    # group (which the nested-tree trainer no longer populates). One
    # Abbreviation/Course Code per subject; one Faculty per (subject, Level
    # 1 node) -- e.g. THEORY and PRACTICALS can have different faculty.
    conn.execute("""
        CREATE TABLE IF NOT EXISTS subject_course_codes_v2 (
            semester_label TEXT NOT NULL,
            subject_index INTEGER NOT NULL,
            subject_name TEXT,
            abbreviation TEXT,
            course_code TEXT,
            UNIQUE(semester_label, subject_index)
        )
    """)
    conn.execute("""
        CREATE TABLE IF NOT EXISTS subject_component_faculty_v2 (
            semester_label TEXT NOT NULL,
            subject_index INTEGER NOT NULL,
            node_id INTEGER NOT NULL,
            component_label TEXT,
            faculty_name TEXT,
            UNIQUE(semester_label, subject_index, node_id)
        )
    """)
    # K7 (Part C) needs a Level 1 branch + two Level 2 leaves (its
    # THEORY/FA-TH/SA-TH equivalents) to compute the FA vs SA Score Index.
    # The label choice itself is global (see save_k7c_labels()/
    # load_k7c_labels()) and lives in report_settings below, alongside
    # Institute Name/Address -- no dedicated table needed.
    #
    # Free-text report settings (Institute Name/Address, K7 (Part C)
    # labels) -- entered once, global across every semester rather than
    # retrained per semester like the box-selected groups.
    conn.execute("""
        CREATE TABLE IF NOT EXISTS report_settings (
            key TEXT PRIMARY KEY,
            value TEXT
        )
    """)
    # Snapshot of the most recent "Yearly Report Gap Check" -- every
    # enrollment that has data for only ONE semester of a YEAR_GROUPS
    # pair (see compute_yearly_semester_gaps()). Replaced wholesale each
    # time a Check is run (see save_yearly_gap_flags_to_db()) rather than
    # accumulated, so it always reflects "as of the last Check", not
    # history. Yearly_Result_Report and Yearly_Eligible_NonEligible_Report
    # are blocked while this is non-empty -- see yearly_reports_are_blocked().
    conn.execute("""
        CREATE TABLE IF NOT EXISTS yearly_gap_flags (
            enrollment TEXT NOT NULL,
            year_label TEXT NOT NULL,
            present_semester TEXT NOT NULL,
            missing_semester TEXT NOT NULL,
            UNIQUE(enrollment, missing_semester)
        )
    """)
    conn.commit()
    conn.close()


def load_report_settings(db_path=DB_FILE):
    """{'institute_name': ..., 'institute_address': ...} -- whatever's
    been saved so far via train mode's Institute Name/Address boxes.
    A key simply isn't in the dict if it's never been entered."""
    if not os.path.exists(db_path):
        return {}
    conn = sqlite3.connect(db_path)
    try:
        rows = conn.execute("SELECT key, value FROM report_settings").fetchall()
    except sqlite3.OperationalError:
        rows = []
    conn.close()
    return dict(rows)


def save_report_settings(settings, db_path=DB_FILE):
    """settings: {key: value} -- upserts each key (re-saving updates the
    existing row rather than duplicating it)."""
    init_db(db_path)
    conn = sqlite3.connect(db_path)
    conn.executemany("""
        INSERT INTO report_settings (key, value) VALUES (?, ?)
        ON CONFLICT(key) DO UPDATE SET value=excluded.value
    """, list(settings.items()))
    conn.commit()
    conn.close()



def save_semester_headings_to_db(sample_extracted, semester_label, db_path=DB_FILE):
    """Save ONE semester's heading facts (subjects/THPRSLA/FASA/
    maximum_marks) to the database, ONCE -- called from train mode right
    after training that semester, using the very sample that defined the
    ranges (the same sample the PDF report's headings are built from). If you
    retrain this semester later, this just overwrites the old facts."""
    init_db(db_path)
    conn = sqlite3.connect(db_path)
    rows = [r for r in sample_extracted if r["group_name"] in HEADING_GROUPS]
    conn.executemany("""
        INSERT INTO semester_headings
            (semester_label, group_name, field_name, range_idx, row_offset, col_offset, abs_row, abs_col, value)
        VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)
        ON CONFLICT(semester_label, group_name, abs_row, abs_col)
        DO UPDATE SET field_name=excluded.field_name, value=excluded.value
    """, [
        (semester_label, r["group_name"], r["field_name"], r.get("range_idx"),
         r.get("row_offset"), r.get("col_offset"), r["abs_row"], r["abs_col"], r["value"])
        for r in rows
    ])
    conn.commit()
    conn.close()


def save_canonical_marks_to_db(canonical_rows, db_path=DB_FILE):
    """Upsert normalized (enrollment, semester, subject, component) rows
    into canonical_marks -- scheme-agnostic storage used for any scheme
    whose raw layout doesn't fit the K-scheme grid-cell tables (currently
    I-scheme; any future scheme's normalize_*_to_canonical() should feed
    here too). Re-running extract on an enrollment already saved UPDATES
    its rows instead of duplicating them, same upsert behavior as the
    rest of the tool's DB writes."""
    if not canonical_rows:
        return
    init_db(db_path)
    conn = sqlite3.connect(db_path)
    conn.executemany("""
        INSERT INTO canonical_marks
            (enrollment, semester_label, scheme, subject_name, component, max_marks, obtained_marks, credits)
        VALUES (?, ?, ?, ?, ?, ?, ?, ?)
        ON CONFLICT(enrollment, semester_label, subject_name, component)
        DO UPDATE SET scheme=excluded.scheme, max_marks=excluded.max_marks,
                       obtained_marks=excluded.obtained_marks, credits=excluded.credits
    """, [
        (r["enrollment"], r["semester_label"], r["scheme"], r["subject_name"], r["component"],
         r.get("max_marks", ""), r.get("obtained_marks", ""), r.get("credits", ""))
        for r in canonical_rows
    ])
    conn.commit()
    conn.close()


def normalize_obtained_total_marks(value):
    """MSBTE sometimes shows Obtained Total Marks as an addition rather
    than a plain number -- e.g. "200+13=213" (base score + grace/
    moderation marks = final total). Only the number AFTER the last '='
    is the actual Obtained Total Marks; the rest is just MSBTE showing
    its arithmetic. Any downstream calculation (compute_percentage_fallback(),
    Topper List ranking, etc.) needs a plain number to work with, so this
    converts "200+13=213" -> "213" at the point of saving -- applied in
    save_records_to_db() so it's enforced uniformly regardless of
    whether the value came from Train/Extract/Recheck (live HTML) or
    Offline Import / CSV (typed/pasted).

    Left COMPLETELY UNCHANGED if there's no '=' in it (already a plain
    number) or if whatever follows the last '=' isn't itself a valid
    number (unexpected format -- safer to leave it untouched than guess).
    """
    if value is None:
        return value
    text = str(value).strip()
    if not text or "=" not in text:
        return value
    tail = text.rsplit("=", 1)[-1].strip()
    try:
        float(tail)
    except ValueError:
        return value
    return tail


def save_records_to_db(all_extracted, all_review, db_path=DB_FILE):
    """Save this run's PER-STUDENT records into student_records --
    identity fields, obtained_marks, summary fields only. Heading-group values
    (subjects/THPRSLA/FASA/maximum_marks) are skipped here on purpose:
    they're constant per semester and already saved once via
    save_semester_headings_to_db() during training, so storing them again
    for every student would just be duplicating the same facts.

    Re-running extract on an enrollment you've already saved UPDATES its
    existing rows (matched on enrollment+semester+subject-row+column)
    instead of creating duplicates -- so re-extracting a corrected student
    later just overwrites their old numbers.
    """
    init_db(db_path)
    conn = sqlite3.connect(db_path)
    data_rows = [r for r in all_extracted if r["group_name"] not in HEADING_GROUPS]
    conn.executemany("""
        INSERT INTO student_records
            (enrollment, semester_label, group_name, field_name,
             range_idx, row_offset, col_offset, abs_row, abs_col, value)
        VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
        ON CONFLICT(enrollment, semester_label, group_name, abs_row, abs_col)
        DO UPDATE SET field_name=excluded.field_name, value=excluded.value
    """, [
        (r["enrollment"], r["semester_label"], r["group_name"], r["field_name"],
         r.get("range_idx"), r.get("row_offset"), r.get("col_offset"),
         r["abs_row"], r["abs_col"],
         normalize_obtained_total_marks(r["value"]) if r["group_name"] == "obtained_total_marks" else r["value"])
        for r in data_rows
    ])

    # Review flags are a snapshot of the latest run, not history worth
    # accumulating -- for any enrollment touched this run, drop its old
    # flags before inserting the fresh ones.
    touched_enrollments = {r["enrollment"] for r in all_extracted} | {r["enrollment"] for r in all_review}
    conn.executemany("DELETE FROM review_records WHERE enrollment = ?",
                      [(enr,) for enr in touched_enrollments])
    conn.executemany("""
        INSERT INTO review_records (enrollment, semester_label, reason)
        VALUES (?, ?, ?)
    """, [(r["enrollment"], r["semester_label"], r["reason"]) for r in all_review])

    conn.commit()
    conn.close()


def load_all_records_from_db(db_path=DB_FILE):
    """Load everything back out in the exact same flat shape as
    all_extracted/all_review -- each semester's headings (loaded once)
    merged back in with every student's own records -- so
    build_semester_structure(), generate_semester_pdf(), count_failed_subjects(),
    and every other function that reads records work completely
    unchanged, same as when records came straight from a fresh extract."""
    if not os.path.exists(db_path):
        return [], []
    conn = sqlite3.connect(db_path)
    conn.row_factory = sqlite3.Row

    headings = [dict(row) for row in conn.execute("SELECT * FROM semester_headings")]
    for r in headings:
        r["enrollment"] = None  # a fact about the semester, not any one student
    student = [dict(row) for row in conn.execute("SELECT * FROM student_records")]
    all_review = [dict(row) for row in conn.execute("SELECT * FROM review_records")]

    conn.close()
    return headings + student, all_review


def load_extracted_enrollments(db_path=DB_FILE):
    """Every distinct enrollment number that has at least one row in
    student_records (i.e. has actually been extracted at least once, in
    at least one semester), sorted. Used by Extract mode to show what's
    already in the database before starting a new run."""
    if not os.path.exists(db_path):
        return []
    conn = sqlite3.connect(db_path)
    try:
        rows = conn.execute(
            "SELECT DISTINCT enrollment FROM student_records ORDER BY enrollment"
        ).fetchall()
    except sqlite3.OperationalError:
        rows = []
    conn.close()
    return [r[0] for r in rows]


def erase_extracted_data(db_path=DB_FILE):
    """Wipes every previously EXTRACTED student result out of the
    database -- student_records, review_records, and the yearly gap
    Check's flags (since those reference enrollments that are about to
    disappear). Deliberately leaves the Train-mode setup intact:
    semester_headings (the trained ranges/subjects), subject_course_codes/
    subject_component_faculty (Course Codes mode entries), and
    report_settings (Institute Name/Address) all survive, since none of
    those are "extracted data" -- they're configuration you'd have to
    redo from scratch otherwise. Returns the number of enrollments that
    were wiped."""
    if not os.path.exists(db_path):
        return 0
    enrollments = load_extracted_enrollments(db_path)
    conn = sqlite3.connect(db_path)
    conn.execute("DELETE FROM student_records")
    conn.execute("DELETE FROM review_records")
    conn.execute("DELETE FROM yearly_gap_flags")
    conn.execute("""
        INSERT INTO report_settings (key, value) VALUES ('yearly_gap_checked', '0')
        ON CONFLICT(key) DO UPDATE SET value=excluded.value
    """)
    conn.commit()
    conn.close()
    return len(enrollments)


def load_subjects_by_semester(db_path=DB_FILE):
    """Every semester's subject list, read from semester_headings' "subjects"
    group (trained once per semester in train mode) -- NOT student_records,
    since subjects are a curriculum fact, the same for every student in a
    semester. Returns a list of (semester_label, [(abs_row, subject_name), ...])
    tuples, sorted by SEMESTER_NAMES order then abs_row (subject order as
    trained)."""
    if not os.path.exists(db_path):
        return []
    conn = sqlite3.connect(db_path)
    conn.row_factory = sqlite3.Row
    rows = conn.execute("SELECT * FROM semester_headings WHERE group_name = 'subjects'").fetchall()
    conn.close()

    by_sem = {}
    for r in rows:
        by_sem.setdefault(r["semester_label"], {})[r["abs_row"]] = r["value"]
    ordered_sems = sorted(by_sem, key=lambda s: SEMESTER_NAMES.index(s) if s in SEMESTER_NAMES else 999)
    return [(sem, [(row, by_sem[sem][row]) for row in sorted(by_sem[sem])]) for sem in ordered_sems]


COMPONENT_ORDER = ["THEORY", "PRACTICALS", "ORAL", "TERM WORK", "SLA"]


def _component_sort_key(component):
    """Sort THEORY/PRACTICALS/ORAL/TERM WORK/SLA in that familiar order;
    anything else (a semester with different THPRSLA wording) sorts after,
    alphabetically."""
    c = (component or "").strip().upper()
    return (COMPONENT_ORDER.index(c) if c in COMPONENT_ORDER else len(COMPONENT_ORDER), c)


def get_subject_components_by_semester(db_path=DB_FILE):
    """For every semester and subject (abs_row), which THPRSLA components
    actually apply to it -- e.g. a subject with no Practicals shouldn't get
    a Practicals-faculty box. Derived purely from semester_headings (no
    student data needed): a component's column applies to a subject if that
    subject's maximum_marks cell in that column isn't '-' (MSBTE's
    not-applicable marker) -- same rule build_semester_structure() uses to
    drop N/A columns from the report.

    Returns a list of (semester_label, [(abs_row, subject_name,
    [component, ...]), ...]) tuples, same order as load_subjects_by_semester().
    """
    subjects_by_sem = load_subjects_by_semester(db_path)
    if not subjects_by_sem:
        return []
    conn = sqlite3.connect(db_path)
    conn.row_factory = sqlite3.Row
    rows = conn.execute(
        "SELECT * FROM semester_headings WHERE group_name IN ('thprsla', 'maximum_marks')"
    ).fetchall()
    conn.close()

    thprsla_by_sem_col = {}
    maxmarks_by_sem_cell = {}
    for r in rows:
        if r["group_name"] == "thprsla":
            thprsla_by_sem_col.setdefault((r["semester_label"], r["abs_col"]), (r["value"] or "").strip())
        else:
            maxmarks_by_sem_cell[(r["semester_label"], r["abs_row"], r["abs_col"])] = r["value"]

    result = []
    for sem, subj_list in subjects_by_sem:
        sem_cols = sorted({c for (s, c) in thprsla_by_sem_col if s == sem})
        subj_with_components = []
        for abs_row, subject_name in subj_list:
            comps = []
            for col in sem_cols:
                val = maxmarks_by_sem_cell.get((sem, abs_row, col))
                if val is not None and not is_dash(val) and str(val).strip() != "":
                    label = thprsla_by_sem_col.get((sem, col), "")
                    if label and label not in comps:
                        comps.append(label)
            if not comps:
                # No maximum_marks trained for this subject's cells (e.g. an
                # older DB) -- don't hide the subject, fall back to one
                # generic field rather than showing nothing.
                comps = ["FACULTY"]
            comps.sort(key=_component_sort_key)
            subj_with_components.append((abs_row, subject_name, comps))
        result.append((sem, subj_with_components))
    return result


def load_subject_component_faculty(db_path=DB_FILE):
    """{(semester_label, abs_row, component): faculty_name} -- whatever's
    already been entered, used to prefill the dialog rather than starting
    from blank."""
    if not os.path.exists(db_path):
        return {}
    conn = sqlite3.connect(db_path)
    conn.row_factory = sqlite3.Row
    try:
        rows = conn.execute("SELECT * FROM subject_component_faculty").fetchall()
    except sqlite3.OperationalError:
        rows = []
    conn.close()
    return {(r["semester_label"], r["abs_row"], r["component"]): r["faculty_name"] for r in rows}


def save_subject_component_faculty_to_db(entries, db_path=DB_FILE):
    """entries: list of {semester_label, abs_row, component, faculty_name}.
    Upserts on (semester_label, abs_row, component) -- re-saving updates
    existing rows instead of duplicating them, same as everywhere else."""
    init_db(db_path)
    conn = sqlite3.connect(db_path)
    conn.executemany("""
        INSERT INTO subject_component_faculty
            (semester_label, abs_row, component, faculty_name)
        VALUES (?, ?, ?, ?)
        ON CONFLICT(semester_label, abs_row, component)
        DO UPDATE SET faculty_name=excluded.faculty_name
    """, [(e["semester_label"], e["abs_row"], e["component"], e["faculty_name"]) for e in entries])
    conn.commit()
    conn.close()


def load_subject_course_codes(db_path=DB_FILE):
    """{(semester_label, abs_row): {"subject_name", "abbreviation", "course_code"}}
    -- whatever's already been entered via run_course_code_entry_dialog(),
    used to prefill it next time rather than starting from blank."""
    if not os.path.exists(db_path):
        return {}
    conn = sqlite3.connect(db_path)
    conn.row_factory = sqlite3.Row
    try:
        rows = conn.execute("SELECT * FROM subject_course_codes").fetchall()
    except sqlite3.OperationalError:
        rows = []
    conn.close()
    return {(r["semester_label"], r["abs_row"]): dict(r) for r in rows}


def course_codes_are_filled(db_path=DB_FILE):
    """True if at least one subject anywhere has BOTH an Abbreviation and a
    Course Code saved -- used to gate K7 (Part B), which displays these
    codes, on that data actually having been entered at least once rather
    than silently generating a report full of blanks. Checks both the v2
    (subject-wise trainer) and legacy v1 stores.
    """
    existing_v2 = load_subject_course_codes_v2(db_path)
    if any((row.get("abbreviation") or "").strip() and (row.get("course_code") or "").strip()
           for row in existing_v2.values()):
        return True
    existing_v1 = load_subject_course_codes(db_path)
    return any((row.get("abbreviation") or "").strip() and (row.get("course_code") or "").strip()
               for row in existing_v1.values())


# --- Course Codes v2 (subject-wise trainer: subjects + component_template) ---

def get_subjects_with_level1_components(db_path=DB_FILE):
    """For every subject-wise-trained semester, its subjects plus which
    Level 1 template nodes actually apply to each one (per the Tree
    Checkboxes step) -- e.g. a Practical-only subject only gets its PR
    node, not TH, so Course Codes only asks for the faculty that's
    actually relevant.

    Returns: [(semester_label, [(subject_index, subject_name,
              [(node_id, label), ...]), ...]), ...], semesters in
    SEMESTER_NAMES order, subjects in subject_index order, nodes in
    template definition order.
    """
    semesters = list_subjectwise_semesters(db_path)
    ordered = sorted(semesters, key=lambda s: SEMESTER_NAMES.index(s) if s in SEMESTER_NAMES else 999)
    result = []
    for sem in ordered:
        subjects = load_subjects(sem, db_path)
        nodes = load_component_template(sem, db_path)
        level1_nodes = [n for n in nodes if n["level"] == 1]
        disabled = load_subject_node_disabled(sem, db_path)
        subj_list = []
        for s in subjects:
            applicable = [(n["node_id"], n["label"]) for n in level1_nodes
                          if (s["subject_index"], n["node_id"]) not in disabled]
            if not applicable:
                applicable = [(0, "FACULTY")]  # no template trained yet -- one generic fallback field
            subj_list.append((s["subject_index"], s["subject_name"], applicable))
        result.append((sem, subj_list))
    return result


def load_subject_course_codes_v2(db_path=DB_FILE):
    """{(semester_label, subject_index): {"subject_name", "abbreviation", "course_code"}}"""
    if not os.path.exists(db_path):
        return {}
    conn = sqlite3.connect(db_path)
    conn.row_factory = sqlite3.Row
    rows = conn.execute("SELECT * FROM subject_course_codes_v2").fetchall()
    conn.close()
    return {(r["semester_label"], r["subject_index"]): dict(r) for r in rows}


def save_subject_course_codes_v2_to_db(entries, db_path=DB_FILE):
    """entries: list of {semester_label, subject_index, subject_name,
    abbreviation, course_code}. Upserts on (semester_label, subject_index)."""
    init_db(db_path)
    conn = sqlite3.connect(db_path)
    conn.executemany("""
        INSERT INTO subject_course_codes_v2
            (semester_label, subject_index, subject_name, abbreviation, course_code)
        VALUES (?, ?, ?, ?, ?)
        ON CONFLICT(semester_label, subject_index)
        DO UPDATE SET subject_name=excluded.subject_name,
                      abbreviation=excluded.abbreviation,
                      course_code=excluded.course_code
    """, [(e["semester_label"], e["subject_index"], e["subject_name"],
           e["abbreviation"], e["course_code"]) for e in entries])
    conn.commit()
    conn.close()


def load_subject_component_faculty_v2(db_path=DB_FILE):
    """{(semester_label, subject_index, node_id): faculty_name}"""
    if not os.path.exists(db_path):
        return {}
    conn = sqlite3.connect(db_path)
    rows = conn.execute(
        "SELECT semester_label, subject_index, node_id, faculty_name FROM subject_component_faculty_v2"
    ).fetchall()
    conn.close()
    return {(r[0], r[1], r[2]): r[3] for r in rows}


def save_subject_component_faculty_v2_to_db(entries, db_path=DB_FILE):
    """entries: list of {semester_label, subject_index, node_id,
    component_label, faculty_name}. Upserts on (semester_label,
    subject_index, node_id)."""
    init_db(db_path)
    conn = sqlite3.connect(db_path)
    conn.executemany("""
        INSERT INTO subject_component_faculty_v2
            (semester_label, subject_index, node_id, component_label, faculty_name)
        VALUES (?, ?, ?, ?, ?)
        ON CONFLICT(semester_label, subject_index, node_id)
        DO UPDATE SET component_label=excluded.component_label, faculty_name=excluded.faculty_name
    """, [(e["semester_label"], e["subject_index"], e["node_id"],
           e["component_label"], e["faculty_name"]) for e in entries])
    conn.commit()
    conn.close()


def save_subject_course_codes_to_db(entries, db_path=DB_FILE):
    """entries: list of {semester_label, abs_row, subject_name, abbreviation,
    course_code, faculty_name}. Upserts on (semester_label, abs_row), same
    "identify by group/row, not cell address" rule as the rest of this
    file -- re-saving updates existing rows instead of duplicating them.
    """
    init_db(db_path)
    conn = sqlite3.connect(db_path)
    conn.executemany("""
        INSERT INTO subject_course_codes
            (semester_label, abs_row, subject_name, abbreviation, course_code, faculty_name)
        VALUES (?, ?, ?, ?, ?, ?)
        ON CONFLICT(semester_label, abs_row)
        DO UPDATE SET subject_name=excluded.subject_name,
                      abbreviation=excluded.abbreviation,
                      course_code=excluded.course_code,
                      faculty_name=excluded.faculty_name
    """, [(e["semester_label"], e["abs_row"], e["subject_name"], e["abbreviation"],
           e["course_code"], e["faculty_name"]) for e in entries])
    conn.commit()
    conn.close()


def apply_clipboard_paste(entry_rows, row_idx, col_idx, clip_text, n_cols):
    """Excel-style paste: given the flat entry_rows grid (each element's
    LAST item is its list of N_COLS cell widgets, each supporting
    .delete(0, END)/.insert(0, text)), fill starting at (row_idx, col_idx)
    with clip_text -- tab-separated columns, newline-separated rows --
    same as pasting a copied Excel range. Silently stops at the edge of
    the grid/columns rather than erroring if the pasted block runs past
    the last subject or past the last column. A cell disabled (state
    "disabled", used for a not-applicable component -- e.g. this subject
    has no Practicals) is skipped rather than written to, but the pasted
    block still advances past it so alignment with the rest of the pasted
    block doesn't shift. Pure/no Tkinter dependency beyond the widgets' own
    delete/insert/cget, so this is unit-testable with plain stand-in
    objects.
    """
    lines = clip_text.replace("\r\n", "\n").replace("\r", "\n").split("\n")
    if lines and lines[-1] == "":
        lines.pop()  # trailing newline from the copied block
    for dr, line in enumerate(lines):
        r = row_idx + dr
        if r >= len(entry_rows):
            break
        cells = line.split("\t")
        for dc, value in enumerate(cells):
            c = col_idx + dc
            if c >= n_cols:
                break
            target = entry_rows[r][-1][c]
            try:
                if str(target.cget("state")) == "disabled":
                    continue
            except Exception:
                pass
            target.delete(0, "end")
            target.insert(0, value.strip())


def run_course_code_entry_dialog(db_path=DB_FILE):
    """"Input course code for each subject" -- a scrollable, Excel-style
    dialog listing every semester's subjects (from semester_headings'
    "subjects" group, trained in train mode): Subject name in the first
    column (read-only, prefilled), Abbreviation / Course Code as editable
    entry boxes, then ONE faculty column per THPRSLA component that
    actually applies to that subject (e.g. Theory Faculty / Practicals
    Faculty / SLA Faculty) -- since MSBTE lets a different faculty teach
    the theory portion of a subject vs. the practical portion, one flat
    "Faculty Name" field can't represent that. A subject with no
    Practicals component simply has that cell greyed out and disabled.
    Re-running this dialog any time (even after data's already been
    filled and extracted) reopens prefilled with whatever was saved last,
    ready to edit and re-save -- nothing about it is one-shot.

    Bulk copy-paste: every subject row across EVERY semester sits in one
    continuous grid. Copy a block of cells from Excel, click into any cell
    here, and paste (Ctrl+V) -- it fills that cell and however many more
    cells the clipboard covers, expanding right across columns and down
    across rows exactly like pasting into Excel itself, including flowing
    across a semester boundary if the pasted block is longer than one
    semester's subject list. Greyed-out (not-applicable) cells are skipped
    but still counted, so column alignment with the rest of the pasted
    block isn't thrown off.

    Saving upserts Abbreviation/Course Code into subject_course_codes and
    each component's faculty into subject_component_faculty, both keyed by
    (semester_label, abs_row, ...) -- portable the same way as everything
    else here, no cell addresses. The very first time this runs after
    upgrading, any old single Faculty Name already saved is copied in as
    the starting value for every component box (so nothing already typed
    in gets lost), unless a component-specific value has already been
    saved for that subject.
    """
    subjects_components_by_sem = get_subject_components_by_semester(db_path)
    if not subjects_components_by_sem:
        print("No subjects found in the database -- run train mode for at least one semester first.")
        return False

    existing_codes = load_subject_course_codes(db_path)
    existing_faculty = load_subject_component_faculty(db_path)

    # Fixed, tool-wide column set: every distinct component seen across
    # every semester/subject, in THEORY/PRACTICALS/ORAL/TERM WORK/SLA
    # order -- keeps the grid rectangular (needed for paste) even though
    # which of these apply varies per subject.
    all_components = []
    for _sem, subj_list in subjects_components_by_sem:
        for _abs_row, _subject_name, comps in subj_list:
            for c in comps:
                if c not in all_components:
                    all_components.append(c)
    all_components.sort(key=_component_sort_key)

    root = tk.Toplevel(_get_app_root())
    root.title("Input course code for each subject")
    root.attributes("-topmost", True)
    try:
        root.state("zoomed")
    except tk.TclError:
        root.geometry("1100x650")

    tk.Label(root, text="Input course code for each subject", font=("Arial", 13, "bold")).pack(
        anchor="w", padx=12, pady=(12, 2))
    tk.Label(root, text="For each subject below, enter its Abbreviation, Course Code, and Faculty for "
                        "each component that applies to it (Theory/Practicals/SLA -- greyed-out boxes "
                        "mean that component doesn't apply to that subject). "
                        "Tip: copy a block of cells from Excel, click a cell here, and paste (Ctrl+V) -- "
                        "it fills across columns and down rows automatically, just like Excel.",
             font=("Arial", 9), wraplength=900, justify="left").pack(anchor="w", padx=12, pady=(0, 8))

    main_frame = tk.Frame(root)
    main_frame.pack(fill="both", expand=True)
    canvas = tk.Canvas(main_frame)
    scrollbar = ttk.Scrollbar(main_frame, orient="vertical", command=canvas.yview)
    scroll_frame = tk.Frame(canvas)
    scroll_frame.bind("<Configure>", lambda e: canvas.configure(scrollregion=canvas.bbox("all")))
    canvas.create_window((0, 0), window=scroll_frame, anchor="nw")
    canvas.configure(yscrollcommand=scrollbar.set)
    canvas.pack(side="left", fill="both", expand=True, padx=(12, 0), pady=5)
    scrollbar.pack(side="left", fill="y")

    def _on_mousewheel(event):
        canvas.yview_scroll(int(-1 * (event.delta / 120)), "units")
    canvas.bind("<Enter>", lambda e: canvas.bind_all("<MouseWheel>", _on_mousewheel))
    canvas.bind("<Leave>", lambda e: canvas.unbind_all("<MouseWheel>"))

    # Columns: Abbreviation, Course Code, then one faculty column per
    # component in all_components.
    N_FIXED_COLS = 2
    N_COLS = N_FIXED_COLS + len(all_components)

    def component_header(c):
        return f"{c.title()} Faculty"

    # entry_rows[i] = (semester_label, abs_row, subject_name, comps, [abbrev_entry, code_entry, *faculty_entries])
    # -- ONE continuous list across every semester, so paste can flow
    # across a semester boundary the same way it flows down a normal
    # column of subjects within one semester.
    entry_rows = []

    for sem, subj_list in subjects_components_by_sem:
        tk.Label(scroll_frame, text=sem.title(), font=("Arial", 11, "bold"),
                 fg="#4472C4").pack(anchor="w", pady=(10, 2))
        header_row = tk.Frame(scroll_frame)
        header_row.pack(fill="x")
        tk.Label(header_row, text="Subject", width=32, anchor="w",
                 font=("Arial", 9, "bold")).grid(row=0, column=0, padx=4)
        tk.Label(header_row, text="Abbreviation", width=14, anchor="w",
                 font=("Arial", 9, "bold")).grid(row=0, column=1, padx=4)
        tk.Label(header_row, text="Course Code", width=14, anchor="w",
                 font=("Arial", 9, "bold")).grid(row=0, column=2, padx=4)
        for i, c in enumerate(all_components):
            tk.Label(header_row, text=component_header(c), width=18, anchor="w",
                     font=("Arial", 9, "bold")).grid(row=0, column=3 + i, padx=4)

        for abs_row, subject_name, comps in subj_list:
            row_frame = tk.Frame(scroll_frame)
            row_frame.pack(fill="x", pady=1)
            tk.Label(row_frame, text=subject_name, width=32, anchor="w").grid(row=0, column=0, padx=4)

            prior_code = existing_codes.get((sem, abs_row), {})
            legacy_faculty = (prior_code.get("faculty_name") or "").strip()
            cell_entries = []

            for col_idx, (key, width) in enumerate(zip(["abbreviation", "course_code"], [16, 16])):
                entry = tk.Entry(row_frame, width=width)
                entry.insert(0, prior_code.get(key) or "")
                entry.grid(row=0, column=col_idx + 1, padx=4)
                cell_entries.append(entry)

            for i, c in enumerate(all_components):
                entry = tk.Entry(row_frame, width=18)
                applicable = c in comps
                if applicable:
                    prior_val = existing_faculty.get((sem, abs_row, c))
                    # First run after upgrading: nothing component-specific
                    # saved yet -- start from the old flat faculty_name
                    # rather than blank, so nothing already typed is lost.
                    entry.insert(0, prior_val if prior_val is not None else legacy_faculty)
                else:
                    entry.insert(0, "N/A")
                    entry.configure(state="disabled", disabledbackground="#e0e0e0",
                                     disabledforeground="#999999")
                entry.grid(row=0, column=3 + i, padx=4)
                cell_entries.append(entry)

            entry_rows.append((sem, abs_row, subject_name, comps, cell_entries))

    # --- Excel-style bulk paste: fills starting at whichever cell the
    # paste happens in, expanding across columns (tab-separated) and down
    # rows (newline-separated) through the flat entry_rows list above,
    # regardless of semester boundaries. Disabled (not-applicable) cells
    # are skipped by apply_clipboard_paste itself. ---
    def make_paste_handler(row_idx, col_idx):
        def handler(event):
            try:
                clip = root.clipboard_get()
            except tk.TclError:
                return "break"
            apply_clipboard_paste(entry_rows, row_idx, col_idx, clip, N_COLS)
            return "break"  # don't also run the default single-cell paste
        return handler

    for row_idx, (_sem, _abs_row, _subject_name, _comps, cell_entries) in enumerate(entry_rows):
        for col_idx, entry in enumerate(cell_entries):
            entry.bind("<<Paste>>", make_paste_handler(row_idx, col_idx))

    result = {"saved": False}

    def submit():
        code_entries = []
        faculty_entries = []
        for sem, abs_row, subject_name, comps, cells in entry_rows:
            code_entries.append({
                "semester_label": sem, "abs_row": abs_row, "subject_name": subject_name,
                "abbreviation": cells[0].get().strip(), "course_code": cells[1].get().strip(),
                # Legacy column: keep it roughly in sync (first applicable
                # component's faculty) purely so an old DB browsed directly
                # still shows something sensible; component table is the
                # real source of truth going forward.
                "faculty_name": cells[N_FIXED_COLS].get().strip() if comps else "",
            })
            for i, c in enumerate(all_components):
                if c not in comps:
                    continue
                faculty_entries.append({
                    "semester_label": sem, "abs_row": abs_row, "component": c,
                    "faculty_name": cells[N_FIXED_COLS + i].get().strip(),
                })
        save_subject_course_codes_to_db(code_entries, db_path)
        save_subject_component_faculty_to_db(faculty_entries, db_path)
        result["saved"] = True
        root.destroy()

    btn_frame = tk.Frame(root)
    btn_frame.pack(pady=10)
    ttk.Button(btn_frame, text="Save", command=submit).pack(side="left", padx=6)
    ttk.Button(btn_frame, text="Cancel", command=root.destroy).pack(side="left", padx=6)
    root.protocol("WM_DELETE_WINDOW", root.destroy)

    root.grab_set()
    root.wait_window()
    if result["saved"]:
        print(f"Saved course codes and per-component faculty for {len(entry_rows)} subject(s) across "
              f"{len(subjects_components_by_sem)} semester(s) to {db_path}.")
    else:
        print("Cancelled -- no changes saved.")
    return result["saved"]



def run_extract_mode():
    """Reads enrollment numbers (one per line, top to bottom, STOPPING at
    the first blank line) from enrollment_list.txt, fetches each live
    (captcha manual again), applies layout_mapping.json, and saves the
    per-student data (identity fields, obtained_marks, summary fields)
    to the database. One enrollment failing doesn't stop the batch --
    it's logged for review and extraction moves on to the next line.
    """
    if not os.path.exists(MAPPING_FILE):
        print(f"Could not find {MAPPING_FILE}. Run 'python msbte_tool.py train' first.")
        return
    mapping = load_mapping()

    if not os.path.exists(ENROLLMENT_LIST_FILE):
        print(f"Could not find {ENROLLMENT_LIST_FILE}.")
        print("Create it with one enrollment number per line, then run this again.")
        return
    with open(ENROLLMENT_LIST_FILE, encoding="utf-8") as f:
        raw_lines = f.readlines()

    # Read enrollment numbers top-to-bottom and STOP at the first blank
    # line -- everything above the blank line is the list; a blank line
    # marks the end of it (so notes/anything typed further down in the
    # file never gets mistaken for an enrollment number and fetched).
    enrollments = []
    for line in raw_lines:
        stripped = line.strip()
        if not stripped:
            break
        enrollments.append(stripped)

    if not enrollments:
        print(f"{ENROLLMENT_LIST_FILE} is empty.")
        return

    session = requests.Session()
    all_extracted = []
    all_canonical = []
    all_subjectwise = []
    all_review = []

    for enr in enrollments:
        print(f"\nFetching {enr} ...")
        try:
            html, attempts = fetch_result_html_with_retry(session, enr)
            if not html:
                all_review.append({"enrollment": enr, "semester_label": None,
                                    "reason": "Fetch/captcha failed."})
                continue
            extracted, canonical_rows, subjectwise_records, review = apply_mapping_to_html(html, mapping, enr, DB_FILE)
            if attempts > 1:
                if extracted or canonical_rows or subjectwise_records:
                    print(f"  Resolved after {attempts} attempt(s) (earlier attempt(s) likely had a wrong captcha).")
                else:
                    print(f"  Still no result tables for {enr} after {attempts} attempts "
                          f"(wrong enrollment number, no result available, or repeated wrong captcha). Skipping.")
            all_extracted.extend(extracted)
            all_canonical.extend(canonical_rows)
            all_subjectwise.extend(subjectwise_records)
            all_review.extend(review)
            print(f"  {len(extracted)} field(s) extracted, {len(subjectwise_records)} subject-wise mark(s) extracted, "
                  f"{len(canonical_rows)} canonical mark(s) extracted, {len(review)} flagged for review.")
        except Exception as e:
            # One enrollment blowing up (network hiccup, unexpected page
            # structure, etc.) must never kill the rest of the batch --
            # log it and move on to the next enrollment number.
            print(f"  ERROR processing {enr}: {e}. Skipping and continuing with the next enrollment.")
            all_review.append({"enrollment": enr, "semester_label": None,
                                "reason": f"Unhandled error during extraction: {e}"})

    save_records_to_db(all_extracted, all_review, DB_FILE)
    save_canonical_marks_to_db(all_canonical, DB_FILE)
    save_subjectwise_student_records_to_db(all_subjectwise, DB_FILE)
    print(f"Saved to database: {DB_FILE}")
    print(f"  Total extracted (k_scheme): {len(all_extracted)}")
    print(f"  Total subject-wise marks (tree trainer): {len(all_subjectwise)}")
    print(f"  Total canonical marks (i_scheme etc.): {len(all_canonical)}")
    print(f"  Total review needed: {len(all_review)}")
    print("Run 'python msbte_tool.py report' to build the PDF report(s) from the database.")


# ==========================================================
# UPDATE MARKS AFTER RECHECKING
# ==========================================================
# A student applies for rechecking, MSBTE revises one or more subject
# marks and possibly the overall Result, and that correction needs to
# land in student_records for whichever enrollment(s) it affects.
#
# Two ways to apply it -- the user picks per run via ask_recheck_method():
#   "automatic" -- re-fetch the live result the same way extract mode
#                  does (captcha included) and overwrite via the same
#                  upsert save_records_to_db() already uses. Simplest,
#                  but only works once MSBTE's own site actually reflects
#                  the revised marks -- if it hasn't been updated there
#                  yet, extraction happily "succeeds" with the OLD
#                  numbers and nothing looks wrong. To catch that,
#                  run_recheck_automatic_mode() snapshots each
#                  enrollment's data before and after and reports whether
#                  anything actually changed.
#   "manual"    -- the user types the corrected marks in directly,
#                  editing a form pre-filled with whatever's currently in
#                  the database, semester by semester. Slower, but immune
#                  to MSBTE's site lagging behind the recheck result.

def ask_recheck_method():
    """Small modal dialog: automatic (re-fetch from MSBTE) vs manual
    (type in the corrected marks) vs Cancel. Returns "automatic",
    "manual", or None."""
    root = tk.Toplevel(_get_app_root())
    root.title("Update Marks After Rechecking")
    root.attributes("-topmost", True)
    root.resizable(False, False)

    tk.Label(root, text="Update Marks After Rechecking", font=("Arial", 12, "bold")).pack(
        padx=16, pady=(14, 4))
    tk.Label(
        root,
        text=("Choose how to apply the revised marks:\n\n"
              "Automatic -- re-fetches each enrollment's result live from the MSBTE\n"
              "website (captcha entry, same as Extract mode) and overwrites the old\n"
              "marks. Simplest, but only works if MSBTE has already updated the\n"
              "result on their site -- if they haven't yet, nothing will look wrong,\n"
              "it'll just silently keep the old marks.\n\n"
              "Manual -- you type the corrected marks in yourself, one enrollment at\n"
              "a time, in a form pre-filled with the current database values. Slower,\n"
              "but always reliable regardless of whether MSBTE's site has caught up."),
        justify="left", font=("Arial", 9), wraplength=460,
    ).pack(padx=16, pady=(0, 12))

    result = {"choice": None}

    def choose(val):
        result["choice"] = val
        root.destroy()

    btn_frame = tk.Frame(root)
    btn_frame.pack(pady=(0, 14))
    ttk.Button(btn_frame, text="Automatic (fetch from website)",
               command=lambda: choose("automatic")).pack(side="left", padx=6)
    ttk.Button(btn_frame, text="Manual (type in marks myself)",
               command=lambda: choose("manual")).pack(side="left", padx=6)
    ttk.Button(btn_frame, text="Cancel", command=root.destroy).pack(side="left", padx=6)

    root.protocol("WM_DELETE_WINDOW", root.destroy)
    root.grab_set()
    root.wait_window()
    return result["choice"]


def _snapshot_student_records(enrollment, db_path=DB_FILE):
    """{key: value} for every student_records row AND every
    subjectwise_student_records row currently saved for this enrollment --
    used to diff before/after an automatic recheck fetch, so a fetch that
    quietly came back with the SAME old numbers (MSBTE hasn't updated the
    site yet) can be told apart from one that actually changed something.
    Both raw tables are covered since a semester trained through the newer
    subject/level tree trainer stores its marks in
    subjectwise_student_records instead of student_records."""
    if not os.path.exists(db_path):
        return {}
    conn = sqlite3.connect(db_path)
    conn.row_factory = sqlite3.Row
    rows = conn.execute("SELECT * FROM student_records WHERE enrollment = ?", (enrollment,)).fetchall()
    snapshot = {("student_records", r["semester_label"], r["group_name"], r["abs_row"], r["abs_col"]): r["value"]
                for r in rows}
    try:
        subj_rows = conn.execute(
            "SELECT * FROM subjectwise_student_records WHERE enrollment = ?", (enrollment,)
        ).fetchall()
    except sqlite3.OperationalError:
        subj_rows = []
    snapshot.update({
        ("subjectwise", r["semester_label"], r["subject_index"], r["node_id"], r["role"]): r["value"]
        for r in subj_rows
    })
    conn.close()
    return snapshot


def run_recheck_automatic_mode(db_path=DB_FILE):
    """Reads enrollment numbers (one per line, stopping at the first
    blank line, same convention as enrollment_list.txt) from
    recheck_list.txt, re-fetches each one live from MSBTE (captcha
    manual, with the same wrong-captcha retry as extract mode), and
    saves the result over the old data via the normal upsert in
    save_records_to_db() -- matched on enrollment+semester+row+column,
    so a corrected value just overwrites the old one in place.

    Snapshots each enrollment's data before and after the fetch and
    reports whether anything actually changed, since a "successful"
    fetch that MSBTE hasn't actually updated yet on their end would
    otherwise look identical to a real, applied correction.
    """
    if not os.path.exists(MAPPING_FILE):
        print(f"Could not find {MAPPING_FILE}. Run 'python msbte_tool.py train' first.")
        return
    mapping = load_mapping()

    if not os.path.exists(RECHECK_LIST_FILE):
        print(f"Could not find {RECHECK_LIST_FILE}.")
        print("Create it with one enrollment number per line (the students whose "
              "rechecking result changed), then run this again.")
        return
    with open(RECHECK_LIST_FILE, encoding="utf-8") as f:
        raw_lines = f.readlines()

    enrollments = []
    for line in raw_lines:
        stripped = line.strip()
        if not stripped:
            break
        enrollments.append(stripped)

    if not enrollments:
        print(f"{RECHECK_LIST_FILE} is empty.")
        return

    session = requests.Session()
    changed_count = 0
    unchanged_count = 0
    failed_count = 0

    for enr in enrollments:
        print(f"\nFetching {enr} ...")
        before = _snapshot_student_records(enr, db_path)
        try:
            html, attempts = fetch_result_html_with_retry(session, enr)
            if not html:
                print(f"  Fetch/captcha failed for {enr}. Skipping.")
                failed_count += 1
                continue

            extracted, canonical_rows, subjectwise_records, review = apply_mapping_to_html(html, mapping, enr, db_path)
            if not extracted and not canonical_rows and not subjectwise_records:
                print(f"  No data extracted for {enr} (wrong enrollment, no mapping for this "
                      f"semester, or no result available). Skipping.")
                failed_count += 1
                continue

            save_records_to_db(extracted, review, db_path)
            save_canonical_marks_to_db(canonical_rows, db_path)
            save_subjectwise_student_records_to_db(subjectwise_records, db_path)
            after = _snapshot_student_records(enr, db_path)
            diff_keys = {k for k in after if before.get(k) != after.get(k)}

            if diff_keys:
                changed_count += 1
                print(f"  Updated: {len(diff_keys)} field(s) changed for {enr}.")
            else:
                unchanged_count += 1
                print(f"  No change detected for {enr} -- MSBTE may not have updated this "
                      f"result yet. Consider the Manual option for this one.")
        except Exception as e:
            print(f"  ERROR processing {enr}: {e}. Skipping and continuing with the next enrollment.")
            failed_count += 1

    print(f"\nRecheck (automatic) complete: {changed_count} updated, "
          f"{unchanged_count} unchanged, {failed_count} failed, out of {len(enrollments)}.")
    if unchanged_count:
        print("For enrollments with no change detected, either re-run this later once MSBTE's "
              "site has updated, or use the Manual option instead.")


def _get_identity_and_summary_snapshot(enrollment, semester_label, records):
    """From this semester's student_records rows, pull the identity line
    (Name/Program/Seat No, read-only display only) as a single dict, for
    context at the top of that semester's block in the manual editor."""
    identity = {}
    for r in records:
        if r["semester_label"] == semester_label and r["group_name"] in IDENTITY_GROUPS:
            identity[r["group_name"]] = r["value"]
    return identity


def run_manual_marks_editor(enrollment, db_path=DB_FILE):
    """The manual-update form for one enrollment: every semester this
    enrollment has data for, each shown as its own block --
    Name/Program/Seat No for context (read-only), then one editable box
    per subject-component obtained mark, then editable boxes for Total
    Marks / Obtained Total / Percentage / Result. Every box is prefilled
    with whatever's currently in the database. "Update Marks and Result"
    saves only the boxes whose value actually changed, straight back into
    student_records via a plain UPDATE (same unique key everywhere else
    uses: enrollment + semester_label + group_name + abs_row + abs_col) --
    everything else about that row (field_name, its position in the
    original table) is left exactly as it was, only the value changes.

    Returns True if anything was saved, False if the dialog was
    cancelled or nothing had changed.
    """
    conn = sqlite3.connect(db_path)
    conn.row_factory = sqlite3.Row
    records = conn.execute(
        "SELECT * FROM student_records WHERE enrollment = ? "
        "ORDER BY semester_label, group_name, abs_row, abs_col",
        (enrollment,)
    ).fetchall()
    conn.close()

    if not records:
        messagebox.showinfo("No data found",
                             f"No existing data found for enrollment {enrollment}.\n"
                             "Run Extract mode for this enrollment first.")
        return False

    semesters_present = sorted(
        {r["semester_label"] for r in records},
        key=lambda s: SEMESTER_NAMES.index(s) if s in SEMESTER_NAMES else 999)

    # Subject names (abs_row -> name) and THPRSLA components (abs_col ->
    # label), per semester -- purely for readable row labels, read from
    # semester_headings (the shared, per-semester curriculum facts), NOT
    # student_records.
    heading_conn = sqlite3.connect(db_path)
    heading_conn.row_factory = sqlite3.Row
    heading_rows = heading_conn.execute(
        "SELECT * FROM semester_headings WHERE semester_label IN ({}) "
        "AND group_name IN ('subjects', 'thprsla')".format(
            ",".join("?" * len(semesters_present))),
        semesters_present
    ).fetchall()
    heading_conn.close()

    subject_name_by_sem_row = {}
    component_by_sem_col = {}
    for r in heading_rows:
        if r["group_name"] == "subjects":
            subject_name_by_sem_row[(r["semester_label"], r["abs_row"])] = r["value"]
        else:
            component_by_sem_col[(r["semester_label"], r["abs_col"])] = (r["value"] or "").strip()

    root = tk.Toplevel(_get_app_root())
    root.title(f"Update Marks After Rechecking -- Enrollment {enrollment}")
    root.attributes("-topmost", True)
    try:
        root.state("zoomed")
    except tk.TclError:
        root.geometry("900x650")

    tk.Label(root, text=f"Update Marks After Rechecking -- Enrollment {enrollment}",
             font=("Arial", 13, "bold")).pack(anchor="w", padx=12, pady=(12, 2))
    tk.Label(root, text="Edit any value below and click \"Update Marks and Result\" -- only "
                        "boxes you actually change get saved.",
             font=("Arial", 9), justify="left").pack(anchor="w", padx=12, pady=(0, 8))

    main_frame = tk.Frame(root)
    main_frame.pack(fill="both", expand=True)
    canvas = tk.Canvas(main_frame)
    scrollbar = ttk.Scrollbar(main_frame, orient="vertical", command=canvas.yview)
    scroll_frame = tk.Frame(canvas)
    scroll_frame.bind("<Configure>", lambda e: canvas.configure(scrollregion=canvas.bbox("all")))
    canvas.create_window((0, 0), window=scroll_frame, anchor="nw")
    canvas.configure(yscrollcommand=scrollbar.set)
    canvas.pack(side="left", fill="both", expand=True, padx=(12, 0), pady=5)
    scrollbar.pack(side="left", fill="y")

    def _on_mousewheel(event):
        canvas.yview_scroll(int(-1 * (event.delta / 120)), "units")
    canvas.bind("<Enter>", lambda e: canvas.bind_all("<MouseWheel>", _on_mousewheel))
    canvas.bind("<Leave>", lambda e: canvas.unbind_all("<MouseWheel>"))

    # editable_fields: list of (semester_label, group_name, abs_row, abs_col, original_value, entry_widget)
    editable_fields = []

    for sem in semesters_present:
        sem_records = [r for r in records if r["semester_label"] == sem]

        tk.Label(scroll_frame, text=sem.title(), font=("Arial", 12, "bold"),
                 fg="#4472C4").pack(anchor="w", pady=(14, 2))

        identity = _get_identity_and_summary_snapshot(enrollment, sem, records)
        identity_text = "   ".join(
            f"{IDENTITY_GROUP_LABELS.get(g, g.title())}: {identity[g]}"
            for g in IDENTITY_GROUPS if identity.get(g))
        if identity_text:
            tk.Label(scroll_frame, text=identity_text, font=("Arial", 9, "italic"),
                     fg="#555555").pack(anchor="w", pady=(0, 6))

        marks_records = sorted(
            [r for r in sem_records if r["group_name"] == "obtained_marks"],
            key=lambda r: (r["abs_row"], r["abs_col"]))

        if marks_records:
            header_row = tk.Frame(scroll_frame)
            header_row.pack(fill="x")
            tk.Label(header_row, text="Subject", width=34, anchor="w",
                     font=("Arial", 9, "bold")).grid(row=0, column=0, padx=4)
            tk.Label(header_row, text="Component", width=16, anchor="w",
                     font=("Arial", 9, "bold")).grid(row=0, column=1, padx=4)
            tk.Label(header_row, text="Marks", width=12, anchor="w",
                     font=("Arial", 9, "bold")).grid(row=0, column=2, padx=4)

            for r in marks_records:
                subject_name = subject_name_by_sem_row.get((sem, r["abs_row"]), f"Row {r['abs_row']}")
                component = component_by_sem_col.get((sem, r["abs_col"]), f"Col {r['abs_col']}")
                row_frame = tk.Frame(scroll_frame)
                row_frame.pack(fill="x", pady=1)
                tk.Label(row_frame, text=subject_name, width=34, anchor="w").grid(row=0, column=0, padx=4)
                tk.Label(row_frame, text=component, width=16, anchor="w").grid(row=0, column=1, padx=4)
                entry = tk.Entry(row_frame, width=12)
                entry.insert(0, r["value"] or "")
                entry.grid(row=0, column=2, padx=4)
                editable_fields.append((sem, "obtained_marks", r["abs_row"], r["abs_col"], r["value"], entry))

        summary_records = {r["group_name"]: r for r in sem_records if r["group_name"] in SUMMARY_GROUPS}
        if summary_records:
            summary_row = tk.Frame(scroll_frame)
            summary_row.pack(fill="x", pady=(8, 2))
            for i, g in enumerate(SUMMARY_GROUPS):
                r = summary_records.get(g)
                if not r:
                    continue
                tk.Label(summary_row, text=SUMMARY_GROUP_LABELS.get(g, g.title()) + ":",
                         font=("Arial", 9, "bold")).grid(row=0, column=2 * i, padx=(0, 4), sticky="e")
                entry = tk.Entry(summary_row, width=14)
                entry.insert(0, r["value"] or "")
                entry.grid(row=0, column=2 * i + 1, padx=(0, 14))
                editable_fields.append((sem, g, r["abs_row"], r["abs_col"], r["value"], entry))

    result = {"saved": False}

    def submit():
        changed = [(sem, group, abs_row, abs_col, entry.get().strip())
                   for sem, group, abs_row, abs_col, orig, entry in editable_fields
                   if entry.get().strip() != (orig or "")]

        if not changed:
            messagebox.showinfo("No changes", "Nothing was changed -- nothing to save.")
            return

        upd_conn = sqlite3.connect(db_path)
        upd_conn.executemany(
            "UPDATE student_records SET value = ? "
            "WHERE enrollment = ? AND semester_label = ? AND group_name = ? "
            "AND abs_row = ? AND abs_col = ?",
            [(new_val, enrollment, sem, group, abs_row, abs_col)
             for sem, group, abs_row, abs_col, new_val in changed]
        )
        upd_conn.commit()
        upd_conn.close()

        result["saved"] = True
        messagebox.showinfo("Updated", f"Updated {len(changed)} field(s) for enrollment {enrollment}.")
        root.destroy()

    btn_frame = tk.Frame(root)
    btn_frame.pack(pady=10)
    ttk.Button(btn_frame, text="Update Marks and Result", command=submit).pack(side="left", padx=6)
    ttk.Button(btn_frame, text="Cancel", command=root.destroy).pack(side="left", padx=6)
    root.protocol("WM_DELETE_WINDOW", root.destroy)

    root.grab_set()
    root.wait_window()
    return result["saved"]


def ask_single_enrollment(title="Update Marks After Rechecking", prompt="Enter enrollment number:"):
    """Small modal text-entry dialog for one enrollment number at a
    time -- used to drive the manual recheck loop (one student, then
    ask for the next). Returns the entered string, or None if
    cancelled/left blank."""
    root = tk.Toplevel(_get_app_root())
    root.title(title)
    root.attributes("-topmost", True)
    root.resizable(False, False)

    tk.Label(root, text=prompt).pack(padx=16, pady=(14, 4))
    var = tk.StringVar()
    entry = tk.Entry(root, textvariable=var, width=28, font=("Arial", 12))
    entry.pack(padx=16, pady=4)
    entry.focus()

    result = {"value": None}

    def submit():
        val = var.get().strip()
        result["value"] = val or None
        root.destroy()

    def cancel():
        result["value"] = None
        root.destroy()

    btn_frame = tk.Frame(root)
    btn_frame.pack(pady=(6, 14))
    ttk.Button(btn_frame, text="OK", command=submit).pack(side="left", padx=6)
    ttk.Button(btn_frame, text="Cancel", command=cancel).pack(side="left", padx=6)
    root.bind("<Return>", lambda e: submit())
    root.protocol("WM_DELETE_WINDOW", cancel)

    root.grab_set()
    root.wait_window()
    return result["value"]


def run_recheck_manual_mode(db_path=DB_FILE):
    """One enrollment at a time: ask for the enrollment number, open the
    editor pre-filled with its current data (run_manual_marks_editor()),
    then ask whether to do another. Keeps going until the user cancels
    the enrollment prompt or answers "No" to doing another one."""
    while True:
        enrollment = ask_single_enrollment()
        if not enrollment:
            break
        run_manual_marks_editor(enrollment, db_path)
        if not messagebox.askyesno("Update another?",
                                    "Update marks for another enrollment number?"):
            break


def run_recheck_mode(db_path=DB_FILE):
    """Entry point for 'python msbte_tool.py recheck' -- asks automatic
    vs manual (see ask_recheck_method()), then hands off accordingly."""
    if not os.path.exists(db_path):
        print(f"Could not find {db_path}. Run 'extract' mode at least once first to populate it.")
        return

    choice = ask_recheck_method()
    if choice == "automatic":
        run_recheck_automatic_mode(db_path)
    elif choice == "manual":
        run_recheck_manual_mode(db_path)
    else:
        print("Cancelled -- no changes made.")


def _render_heading_lines(lines):
    """Turn a list of "line" dicts into reportlab Flowables -- no visible
    grid lines anywhere, even for a line that needs a left+right split
    (that uses a Table purely for column alignment, with every border
    style deliberately omitted).

    Each item in `lines` is one of:
        None                                -- a blank line
        {"text": str, "align": "LEFT"|"CENTER"|"RIGHT",
         "bold": bool (optional), "size": int (optional)}
                                             -- one full-width line
        {"left": str, "right": str, "bold": bool (optional)}
                                             -- split line, left+right on the same row
    """
    from reportlab.platypus import Paragraph, Spacer, Table, TableStyle
    from reportlab.lib.styles import getSampleStyleSheet
    from reportlab.lib.enums import TA_LEFT, TA_CENTER, TA_RIGHT
    from reportlab.lib.units import mm

    ss = getSampleStyleSheet()
    base = ss["Normal"].clone("rpthead")
    base.fontSize = 11
    base.leading = 14
    align_map = {"LEFT": TA_LEFT, "CENTER": TA_CENTER, "RIGHT": TA_RIGHT}

    flowables = []
    for line in lines:
        if line is None:
            flowables.append(Spacer(1, 11))
            continue
        if "left" in line or "right" in line:
            left_style = base.clone(f"rpthead_l_{len(flowables)}")
            left_style.alignment = TA_LEFT
            right_style = base.clone(f"rpthead_r_{len(flowables)}")
            right_style.alignment = TA_RIGHT
            if line.get("bold"):
                left_style.fontName = "Helvetica-Bold"
                right_style.fontName = "Helvetica-Bold"
            tbl = Table([[Paragraph(line.get("left") or "&nbsp;", left_style),
                          Paragraph(line.get("right") or "&nbsp;", right_style)]],
                        colWidths=[144.5 * mm, 144.5 * mm])
            tbl.setStyle(TableStyle([
                ("LEFTPADDING", (0, 0), (-1, -1), 0),
                ("RIGHTPADDING", (0, 0), (-1, -1), 0),
                ("TOPPADDING", (0, 0), (-1, -1), 1),
                ("BOTTOMPADDING", (0, 0), (-1, -1), 1),
                # deliberately no GRID/BOX/LINE commands -- invisible borders
            ]))
            flowables.append(tbl)
        else:
            style = base.clone(f"rpthead_{line.get('align', 'LEFT')}_{len(flowables)}")
            style.alignment = align_map.get(line.get("align", "LEFT"), TA_LEFT)
            if line.get("bold"):
                style.fontName = "Helvetica-Bold"
            if line.get("size"):
                style.fontSize = line["size"]
                style.leading = line["size"] + 3
            flowables.append(Paragraph(line.get("text", "") or "&nbsp;", style))
    return flowables


def _common_heading_lines(semester_label, db_path=DB_FILE, include_exam_session=True):
    """Rows 4-7 of the common report heading -- Institute Name+Address /
    Program / Academic Year / Exam Session -- shared by the Semester-wise,
    Yearly Result, and Yearly Eligible/Non-Eligible reports, all centre-
    aligned. Institute Name/Address come from report_settings (typed
    once in train mode); Program and Year come from
    get_semester_identity_text() for the given semester, with Year parsed
    via parse_exam_session(). Any piece that isn't available yet (e.g. an
    older mapping trained before Year/Institute Name existed) is simply
    left out rather than shown as an empty line.

    include_exam_session=False drops row 7 (Exam Summer/Winter) entirely
    -- used by the Yearly Result and Yearly Eligible/Non-Eligible reports,
    which span more than one semester's exam sitting, unlike the
    Semester-wise report where a single Exam Session is always accurate.
    """
    settings = load_report_settings(db_path)
    name = (settings.get("institute_name") or "").strip()
    address = (settings.get("institute_address") or "").strip()

    lines = []
    if name or address:
        combined = ", ".join(p for p in (name, address) if p)
        lines.append({"text": combined, "align": "CENTER", "bold": True})
    if semester_label:
        program = get_semester_identity_text(semester_label, "program", db_path)
        if program:
            lines.append({"text": program, "align": "CENTER"})
        _, _, academic_year, exam_label = parse_exam_session(
            get_semester_identity_text(semester_label, "year", db_path))
        if academic_year:
            lines.append({"text": f"Academic Year: {academic_year}", "align": "CENTER"})
        if include_exam_session and exam_label:
            lines.append({"text": f"Exam: {exam_label}", "align": "CENTER"})
    return lines


def build_semesterwise_heading_flowables(semester_label, db_path=DB_FILE):
    """Row 1 "Semesterwise Report" (centered) / blank / blank / rows 4-7
    the common Institute Name+Address / Program / Academic Year / Exam
    Session block, all centred -- see _common_heading_lines() -- then
    one more centred row naming the semester itself (e.g. "Third
    Semester"), so the report heading reads which semester this PDF is
    for without the reader having to find it in the data table below."""
    from reportlab.platypus import Spacer
    lines = [{"text": "Semesterwise Report", "align": "CENTER", "bold": True, "size": 14}, None, None]
    lines += _common_heading_lines(semester_label, db_path)
    if semester_label:
        lines.append({"text": semester_label.title(), "align": "CENTER", "bold": True})
    flowables = _render_heading_lines(lines)
    flowables.append(Spacer(1, 10))
    return flowables


def build_yearly_result_heading_flowables(semester_label, db_path=DB_FILE):
    """Row 1 "Yearly_Result_Report" (centered) / blank / blank / rows 4-6
    the common Institute Name+Address / Program / Academic Year block,
    centred -- see _common_heading_lines() -- but NOT row 7 (Exam
    Summer/Winter), since this report spans every semester at once.
    semester_label is whichever semester's Program/Year should represent
    the report (generate_yearly_result_pdf uses the latest semester
    found in the database)."""
    from reportlab.platypus import Spacer
    lines = [{"text": "Yearly_Result_Report", "align": "CENTER", "bold": True, "size": 14}, None, None]
    lines += _common_heading_lines(semester_label, db_path, include_exam_session=False)
    flowables = _render_heading_lines(lines)
    flowables.append(Spacer(1, 10))
    return flowables


def build_yearly_eligibility_heading_flowables(semester_label, db_path=DB_FILE):
    """Row 1 "Yearly_Eligible_NonEligible_Report" (centered) / blank /
    blank / rows 4-6 the common Institute Name+Address / Program /
    Academic Year block, centred -- see _common_heading_lines() -- but
    NOT row 7 (Exam Summer/Winter), same reasoning as the Yearly Result
    report. semester_label is whichever semester's Program/Year should
    represent the report (generate_yearly_eligibility_pdf uses the
    latest semester found in the database)."""
    from reportlab.platypus import Spacer
    lines = [{"text": "Yearly_Eligible_NonEligible_Report", "align": "CENTER", "bold": True, "size": 14},
              None, None]
    lines += _common_heading_lines(semester_label, db_path, include_exam_session=False)
    flowables = _render_heading_lines(lines)
    flowables.append(Spacer(1, 10))
    return flowables


def build_topper_list_heading_flowables(semester_label, db_path=DB_FILE):
    """Row 1 "Semesterwise and Yearly Topper List" (centered) / blank /
    blank / rows 4-6 the common Institute Name+Address / Program /
    Academic Year block, centred -- see _common_heading_lines() -- but
    NOT row 7 (Exam Summer/Winter), same reasoning as the Yearly Result
    and Yearly Eligible/Non-Eligible reports (this one spans every
    semester and year at once too). semester_label is whichever
    semester's Program/Year should represent the report
    (generate_topper_list_pdf uses the latest semester found in the
    database)."""
    from reportlab.platypus import Spacer
    lines = [{"text": "Semesterwise and Yearly Topper List", "align": "CENTER", "bold": True, "size": 14},
              None, None]
    lines += _common_heading_lines(semester_label, db_path, include_exam_session=False)
    flowables = _render_heading_lines(lines)
    flowables.append(Spacer(1, 10))
    return flowables


def build_bright_weak_heading_flowables(semester_label, db_path=DB_FILE):
    """Row 1 "Semester wise Bright/Weak Student List" (centered) / blank /
    blank / rows 4-6 the common Institute Name+Address / Program /
    Academic Year block, centred -- see _common_heading_lines() -- but
    NOT row 7 (Exam Summer/Winter), since this report spans every
    semester at once (same reasoning as the Yearly Result / Yearly
    Eligible / Topper List reports). semester_label is whichever
    semester's Program/Year should represent the report
    (generate_bright_weak_pdf uses the latest semester found in the
    database)."""
    from reportlab.platypus import Spacer
    lines = [{"text": "Semester wise Bright/Weak Student List", "align": "CENTER", "bold": True, "size": 14},
              None, None]
    lines += _common_heading_lines(semester_label, db_path, include_exam_session=False)
    flowables = _render_heading_lines(lines)
    flowables.append(Spacer(1, 10))
    return flowables


def build_k7b_heading_flowables(semester_label=None, db_path=DB_FILE):
    """K7 (Part B)'s fixed masthead -- static text: "K7 (Part B)"
    (right), "For AICTE Diploma Engineering Courses" (left) /
    "wef - 2023-24" (right) on the same line, then "Maharashtra State
    Board of Technical Education" and "ANALYSIS OF TERM END EXAMINATION
    RESULT", centre-aligned -- PLUS, right after that, the same common
    heading block used by the Semesterwise/Yearly Result reports
    (Institute Name+Address / Program / Academic Year, centred -- see
    _common_heading_lines()) -- including Exam Session (e.g. "Exam:
    Summer 2026"), centred."""
    from reportlab.platypus import Spacer
    lines = [
        {"text": "K7 (Part B)", "align": "RIGHT", "bold": True},
        {"left": "For AICTE Diploma Engineering Courses", "right": "wef - 2023-24"},
        {"text": "Maharashtra State Board of Technical Education", "align": "CENTER", "bold": True},
        {"text": "ANALYSIS OF TERM END EXAMINATION RESULT", "align": "CENTER", "bold": True},
    ]
    lines += _common_heading_lines(semester_label, db_path, include_exam_session=True)
    flowables = _render_heading_lines(lines)
    flowables.append(Spacer(1, 10))
    return flowables


def build_k7c_heading_flowables(semester_label=None, db_path=DB_FILE):
    """Same fixed masthead as K7 (Part B) except the title ("K7 (Part
    C)") and the closing line ("TH_FA AND TH-SA ANALYSIS" instead of
    "ANALYSIS OF TERM END EXAMINATION RESULT") -- PLUS, right after
    that, the same common heading block used by the Semesterwise/Yearly
    Result reports (Institute Name+Address / Program / Academic Year /
    Exam Session, centred -- see _common_heading_lines())."""
    from reportlab.platypus import Spacer
    lines = [
        {"text": "K7 (Part C)", "align": "RIGHT", "bold": True},
        {"left": "For AICTE Diploma Engineering Courses", "right": "wef - 2023-24"},
        {"text": "Maharashtra State Board of Technical Education", "align": "CENTER", "bold": True},
        {"text": "TH_FA AND TH-SA ANALYSIS", "align": "CENTER", "bold": True},
    ]
    lines += _common_heading_lines(semester_label, db_path, include_exam_session=True)
    flowables = _render_heading_lines(lines)
    flowables.append(Spacer(1, 10))
    return flowables


def build_report_end_flowables():
    """The signature block appended once at the end of a report's content
    (its last page, NOT repeated on every page): 3 blank lines, then
    "Signature of Academic Co-ordinator" (left) / "Signature of HoD"
    (right) on one line, "Name" (left) / "Name" (right) on the next, 2
    more blank lines, then "Signature" (left-aligned). Shared by every
    report.
    """
    from reportlab.platypus import Spacer
    lines = [
        None, None, None,
        {"left": "Signature of Academic Co-ordinator", "right": "Signature of HoD"},
        {"left": "Name", "right": "Name"},
        None, None,
        {"text": "Signature", "align": "LEFT"},
    ]
    flowables = _render_heading_lines(lines)
    flowables.insert(0, Spacer(1, 14))
    return flowables


def generate_semester_pdf(semester_label, db_path=DB_FILE, out_path=None, student_status="both"):
    """Build the semester-wise report: the report heading block first
    (Semesterwise Report / Institute Name+Address / Program / Academic
    Year / Exam Session -- see build_semesterwise_heading_flowables()),
    then a small Result-summary table -- header, then a "Total Appeared
    Students" row, then one row per distinct Result value found for this
    semester (e.g. "FIRST CLASS"/"SECOND CLASS"/"FAIL", most common first
    -- see compute_result_summary_rows()), then a closing "Total" row
    summing those same counts back up as a check -- then 4 heading rows
    -- Subject / TH-PR-SLA / FA-SA / Max Marks, tiled per subject -- then
    one data row per enrollment, with a leading Sr.No. column, then the
    signature block at the very end (see build_report_end_flowables()) --
    as a print-ready landscape A4 PDF, read straight from the database.
    No Excel involved anywhere in this path.

    student_status: "both" (default), "regular", or "ex" -- filters which
    enrollments appear in this semester's report based on
    compute_student_status(): "regular" keeps only enrollments for whom
    this IS their highest semester reached anywhere in the database;
    "ex" keeps only enrollments who have since moved on to a higher
    semester than this one (a backlog/re-appear entry for this semester).

    All columns are forced onto ONE page width -- column widths are
    computed to sum exactly to the page width, and font size/padding shrink
    automatically as more subject columns are added. If there are enough
    students that the table runs past one page vertically, it simply
    continues onto further pages with the same column widths and the
    4 heading rows repeated (repeatRows) -- but the columns themselves are
    never split across pages.
    """
    from reportlab.lib.pagesizes import A4, landscape
    from reportlab.platypus import SimpleDocTemplate, Table, TableStyle, Paragraph, Spacer
    from reportlab.lib.styles import getSampleStyleSheet
    from reportlab.lib import colors
    from reportlab.lib.units import mm

    all_extracted, all_review = load_all_records_from_db(db_path)
    sem_records = [r for r in all_extracted if r["semester_label"] == semester_label]
    if not sem_records:
        print(f"No data found for '{semester_label}' in {db_path}.")
        return None

    status_map = compute_student_status(all_extracted, db_path)

    # identity/summary fields (Name, Enrollment No, Total Marks, Result,
    # etc.) always come from the flat student_records/semester_headings
    # tables, regardless of which trainer the subject-wise marks came
    # from -- build_semester_structure() still owns those, plus the OLD
    # flat mark columns for a semester that hasn't been retrained through
    # the newer tree trainer.
    structure = build_semester_structure(sem_records)

    is_subjectwise = semester_label in list_subjectwise_semesters(db_path)
    if is_subjectwise:
        subj_structure = build_semester_structure_subjectwise(semester_label, db_path)
        columns = subj_structure["columns"]
        n_levels = subj_structure["max_levels"]
        obtained_by_enr_col = subj_structure["obtained_by_enr_col"]
    else:
        columns = structure["columns"]  # tiled subject-block columns, in order
        n_levels = 2
    n_header_rows = n_levels + 2  # Subject row + N level rows + Max Marks row

    obtained_by_enr_cell = {}
    identity_by_group_enr = {g: {} for g in IDENTITY_GROUPS}
    summary_by_group_enr = {g: {} for g in SUMMARY_GROUPS}
    for rec in sem_records:
        gname = rec["group_name"]
        if gname in identity_by_group_enr:
            identity_by_group_enr[gname].setdefault(rec["enrollment"], {})[rec["field_name"]] = rec["value"]
        elif gname in summary_by_group_enr:
            summary_by_group_enr[gname].setdefault(rec["enrollment"], {})[rec["field_name"]] = rec["value"]
        elif gname == "obtained_marks":
            obtained_by_enr_cell.setdefault(rec["enrollment"], {})[(rec["abs_row"], rec["abs_col"])] = rec["value"]

    enrollments = sorted({r["enrollment"] for r in sem_records if r["enrollment"]})
    if student_status in ("regular", "ex"):
        wanted = "Regular" if student_status == "regular" else "EX"
        enrollments = [enr for enr in enrollments if status_map.get((enr, semester_label)) == wanted]
        if not enrollments:
            print(f"No '{wanted}' enrollments found for '{semester_label}' in {db_path}.")
            return None

    # Seating-chart gap check: catches an enrollment the seating chart
    # lists for this semester+status but for which no marks data ever
    # got Trained/Extracted/Offline-imported. That student is NOT added
    # to the table -- the report only ever shows enrollments that
    # actually have data in the database. Instead, the red warning line
    # below (seating_chart_gap_note_lines) names exactly which
    # enrollment number(s) are missing, so the gap is visible without
    # cluttering the table with blank rows.
    seating_gap = compute_seating_chart_gap([semester_label], student_status, set(enrollments))

    # Only groups that actually have trained fields get a column block --
    # older mappings without every group trained yet just won't show those
    # blocks, no error. "enrollment_number" is deliberately EXCLUDED here
    # even when it has trained/imported fields (Offline Import always
    # saves one) -- this table already has its own dedicated, always-
    # present "Enrollment No" column (see header_rows[0] below), so
    # including it again here would print the heading twice.
    active_identity_groups = [g for g in IDENTITY_GROUPS
                               if g != "enrollment_number" and structure["identity_fields"][g]]
    n_seat = sum(len(structure["identity_fields"][g]) for g in active_identity_groups)
    active_summary_groups = [g for g in SUMMARY_GROUPS if structure["summary_fields"][g]]
    n_summary = sum(len(structure["summary_fields"][g]) for g in active_summary_groups)
    n_subject_cols = len(columns)

    page_size = landscape(A4)
    page_w_mm = 297
    margin_mm = 4
    usable_w_mm = page_w_mm - 2 * margin_mm

    # --- Compute column widths that sum EXACTLY to the usable page width.
    # Identity/summary columns get a reasonable starting width (they hold
    # longer text); whatever's left is split evenly across subject columns.
    # If that leaves subject columns below a practical minimum, shrink the
    # identity/summary columns instead, so subjects still get a fair share. ---
    enroll_w, seat_w, summary_w = 16.0, 14.0, 12.0
    srno_w = 8.0
    MIN_SUBJECT_COL_W = 4.5  # mm -- practical floor before text becomes unreadable even wrapped

    identity_total = srno_w + enroll_w + seat_w * n_seat + summary_w * n_summary
    remaining = usable_w_mm - identity_total
    subject_col_w = remaining / n_subject_cols if n_subject_cols else 0

    if n_subject_cols and subject_col_w < MIN_SUBJECT_COL_W:
        subject_col_w = MIN_SUBJECT_COL_W
        remaining_for_identity = usable_w_mm - subject_col_w * n_subject_cols
        scale = max(0.3, remaining_for_identity / identity_total) if identity_total else 1
        srno_w *= scale
        enroll_w *= scale
        seat_w *= scale
        summary_w *= scale

    # --- Font size shrinks as subject columns get narrower. ---
    if not n_subject_cols or subject_col_w >= 9:
        font_size = 7
    elif subject_col_w >= 7:
        font_size = 6
    elif subject_col_w >= 5.5:
        font_size = 5
    else:
        font_size = 4
    leading = font_size + 1

    from reportlab.lib.enums import TA_CENTER, TA_LEFT

    styles = getSampleStyleSheet()
    cell_style = styles["Normal"].clone("cell")
    cell_style.fontSize = font_size
    cell_style.leading = leading
    cell_style.alignment = TA_CENTER
    left_cell_style = cell_style.clone("cellleft")
    left_cell_style.alignment = TA_LEFT
    header_style = cell_style.clone("cellhdr")
    header_style.fontName = "Helvetica-Bold"
    header_style.alignment = TA_CENTER

    def P(text, style=cell_style):
        return Paragraph(str(clean_value(text)) if text not in (None, "") else "&nbsp;", style)

    # Abbreviate long THPRSLA labels so narrow columns don't force excess wrapping.
    ABBR = {"THEORY": "TH", "PRACTICAL": "PR", "SESSIONAL": "SL"}

    def abbr(v):
        return ABBR.get(str(v).strip().upper(), v)

    status_suffix = {"regular": "_Regular", "ex": "_EX", "both": ""}.get(student_status, "")
    out_path = out_path or f"{semester_label.title().replace(' ', '_')}_Report{status_suffix}.pdf"
    doc = SimpleDocTemplate(out_path, pagesize=page_size,
                             leftMargin=margin_mm * mm, rightMargin=margin_mm * mm,
                             topMargin=margin_mm * mm, bottomMargin=margin_mm * mm)
    story = build_semesterwise_heading_flowables(semester_label, db_path)

    result_summary = compute_result_summary_rows(semester_label, db_path, student_status)
    if result_summary:
        # Deliberately its own fixed-size styles, not the main table's
        # cell_style/header_style -- those shrink (down to 4pt) as more
        # subject columns get crammed onto one page, which would make
        # this small summary illegibly tiny.
        res_style = styles["Normal"].clone("rescell")
        res_style.fontSize = 9
        res_style.leading = 11
        res_style.alignment = TA_CENTER
        res_left_style = res_style.clone("resleft")
        res_left_style.alignment = TA_LEFT
        res_header_style = res_style.clone("reshdr")
        res_header_style.fontName = "Helvetica-Bold"

        def RP(text, style=res_style):
            return Paragraph(str(text) if text not in (None, "") else "&nbsp;", style)

        total_appeared = sum(count for _, count in result_summary)
        res_bold_left = res_left_style.clone("resboldleft")
        res_bold_left.fontName = "Helvetica-Bold"
        res_bold = res_style.clone("resbold")
        res_bold.fontName = "Helvetica-Bold"

        res_data = [[RP("Sr. No.", res_header_style), RP("Result", res_header_style), RP("Count", res_header_style)]]
        res_data.append([RP(""), RP("Total Appeared Students", res_bold_left), RP(total_appeared, res_bold)])
        for sr_no, (result_text, count) in enumerate(result_summary, start=1):
            res_data.append([RP(sr_no), RP(result_text, res_left_style), RP(count)])
        res_data.append([RP(""), RP("Total", res_bold_left), RP(total_appeared, res_bold)])

        res_table = Table(res_data, colWidths=[15 * mm, 60 * mm, 25 * mm])
        res_table.setStyle(TableStyle([
            ("GRID", (0, 0), (-1, -1), 0.3, colors.grey),
            ("BACKGROUND", (0, 0), (-1, 0), colors.HexColor("#4472C4")),
            ("TEXTCOLOR", (0, 0), (-1, 0), colors.white),
            ("BACKGROUND", (0, 1), (-1, 1), colors.HexColor("#D9E2F3")),
            ("BACKGROUND", (0, -1), (-1, -1), colors.HexColor("#D9E2F3")),
            ("VALIGN", (0, 0), (-1, -1), "MIDDLE"),
            ("LEFTPADDING", (0, 0), (-1, -1), 3),
            ("RIGHTPADDING", (0, 0), (-1, -1), 3),
            ("TOPPADDING", (0, 0), (-1, -1), 1.5),
            ("BOTTOMPADDING", (0, 0), (-1, -1), 1.5),
        ]))
        story.append(res_table)
        story.append(Spacer(1, 8))

    gap_style = styles["Normal"].clone("gapnote")
    gap_style.fontSize = 8
    gap_warn_style = gap_style.clone("gapwarn")
    gap_warn_style.textColor = colors.HexColor("#B30000")
    for i, line in enumerate(seating_chart_gap_note_lines(seating_gap)):
        story.append(Paragraph(line, gap_warn_style if i > 0 else gap_style))
    story.append(Spacer(1, 6))

    col_widths = ([srno_w * mm, enroll_w * mm] + [seat_w * mm] * n_seat
                  + [subject_col_w * mm] * n_subject_cols + [summary_w * mm] * n_summary)

    header_rows = [[] for _ in range(n_header_rows)]
    header_rows[0] = [P("Sr.No.", header_style), P("Enrollment No", header_style)]
    for g in active_identity_groups:
        label = IDENTITY_GROUP_LABELS[g]
        for _ in structure["identity_fields"][g]:
            header_rows[0].append(P(label, header_style))
    for r in range(1, n_header_rows):
        header_rows[r] = [P("", header_style)] * (2 + n_seat)
    if is_subjectwise:
        for c in columns:
            header_rows[0].append(P(c["subject_label"], header_style))
            for lvl in range(n_levels):
                header_rows[1 + lvl].append(P(c["level_labels"][lvl], header_style))
            header_rows[n_header_rows - 1].append(P(c["max_label"], header_style))
    else:
        for c in columns:
            subj = structure["subject_by_row"].get(c["subject_row"], "")
            th = abbr(structure["thprsla_by_col"].get(c["obt_col"], ""))
            fa = structure["fasa_by_col"].get(c["obt_col"], "")
            mx = structure["maxmarks_by_cell"].get((c["subject_row"], c["max_col"]), "")
            header_rows[0].append(P(subj, header_style))
            header_rows[1].append(P(th, header_style))
            header_rows[2].append(P(fa, header_style))
            header_rows[3].append(P(mx, header_style))
    for g in active_summary_groups:
        label = SUMMARY_GROUP_LABELS[g]
        for _ in structure["summary_fields"][g]:
            for r in range(n_header_rows):
                header_rows[r].append(P(label if r == 0 else "", header_style))

    def _first_value(fields_by_name):
        """First field's value for a summary group -- these are expected
        to be single-value groups (Total Marks, Obtained Total Marks
        etc.), so this is just a safe way to pull that one value out."""
        if not fields_by_name:
            return ""
        return fields_by_name[sorted(fields_by_name)[0]]

    table_data = list(header_rows)
    for sr_no, enr in enumerate(enrollments, start=1):
        row = [P(sr_no), P(enr)]
        for g in active_identity_groups:
            style = left_cell_style if g in ("program", "name") else cell_style
            for field in structure["identity_fields"][g]:
                row.append(P(identity_by_group_enr[g].get(enr, {}).get(field, ""), style))
        for c in columns:
            if is_subjectwise:
                row.append(P(obtained_by_enr_col.get(enr, {}).get(c["col_key"], "")))
            else:
                row.append(P(obtained_by_enr_cell.get(enr, {}).get((c["subject_row"], c["obt_col"]), "")))
        for g in active_summary_groups:
            for field in structure["summary_fields"][g]:
                value = summary_by_group_enr[g].get(enr, {}).get(field, "")
                if g == "percentage" and not value:
                    # Percentage field came back blank -- compute it from
                    # Total Marks / Obtained Total Marks instead of
                    # leaving it blank, if both of those are available.
                    computed = compute_percentage_fallback(
                        _first_value(summary_by_group_enr.get("total_marks", {}).get(enr, {})),
                        _first_value(summary_by_group_enr.get("obtained_total_marks", {}).get(enr, {})),
                    )
                    if computed is not None:
                        value = computed
                row.append(P(value))
        table_data.append(row)

    t = Table(table_data, colWidths=col_widths, repeatRows=n_header_rows)
    style_cmds = [
        ("GRID", (0, 0), (-1, -1), 0.3, colors.grey),
        ("BACKGROUND", (0, 0), (-1, n_header_rows - 1), colors.HexColor("#4472C4")),
        ("TEXTCOLOR", (0, 0), (-1, n_header_rows - 1), colors.white),
        ("VALIGN", (0, 0), (-1, -1), "MIDDLE"),
        ("LEFTPADDING", (0, 0), (-1, -1), 1),
        ("RIGHTPADDING", (0, 0), (-1, -1), 1),
        ("TOPPADDING", (0, 0), (-1, -1), 1),
        ("BOTTOMPADDING", (0, 0), (-1, -1), 1),
        ("SPAN", (0, 0), (0, n_header_rows - 1)),
        ("SPAN", (1, 0), (1, n_header_rows - 1)),
    ]
    # Each identity group gets its own merged header-row block, in
    # sequence, right after Sr.No. / Enrollment No.
    identity_col_idx = 2
    for g in active_identity_groups:
        n_fields = len(structure["identity_fields"][g])
        if n_fields:
            style_cmds.append(("SPAN", (identity_col_idx, 0), (identity_col_idx + n_fields - 1, n_header_rows - 1)))
        identity_col_idx += n_fields

    # --- Merge repeated Subject cells (row 0) and repeated level-label
    # cells across the columns they span, instead of repeating the text
    # in every column -- same idea as a printed mark sheet's merged banner. ---
    subject_block_start = 2 + n_seat

    def merge_runs(values, header_row_idx):
        run_start = 0
        for i in range(1, len(values) + 1):
            if i == len(values) or values[i] != values[run_start]:
                if i - run_start > 1:
                    col_from = subject_block_start + run_start
                    col_to = subject_block_start + i - 1
                    style_cmds.append(("SPAN", (col_from, header_row_idx), (col_to, header_row_idx)))
                run_start = i

    if is_subjectwise:
        subject_values = [c["subject_key"] for c in columns]
        merge_runs(subject_values, 0)
        # Each level row merges independently -- level_keys already fold
        # in the subject index, so a run never merges across a subject
        # boundary, and padded (blank) cells never merge with real ones
        # since each pad cell has a unique key.
        for lvl in range(n_levels):
            level_values = [c["level_keys"][lvl] for c in columns]
            merge_runs(level_values, 1 + lvl)
    else:
        subject_values = [c["subject_row"] for c in columns]
        merge_runs(subject_values, 0)

        # TH/PR/SLA runs should never merge across a subject boundary, so key
        # on (subject_row, th_value) together -- a run only continues while
        # BOTH stay the same.
        th_values = [(c["subject_row"], abbr(structure["thprsla_by_col"].get(c["obt_col"], "")))
                     for c in columns]
        merge_runs(th_values, 1)

    summary_col_idx = subject_block_start + n_subject_cols
    for g in active_summary_groups:
        n_fields = len(structure["summary_fields"][g])
        style_cmds.append(("SPAN", (summary_col_idx, 0), (summary_col_idx + n_fields - 1, n_header_rows - 1)))
        summary_col_idx += n_fields

    t.setStyle(TableStyle(style_cmds))
    story.append(t)
    story.extend(build_report_end_flowables())

    doc.build(story)
    actual_width_mm = sum(col_widths) / mm
    print(f"Saved PDF: {out_path}  (landscape A4, {len(enrollments)} enrollment(s) "
          f"[{student_status}], {n_subject_cols} subject columns @ {subject_col_w:.1f}mm, "
          f"{font_size}pt font, table width {actual_width_mm:.0f}mm of {usable_w_mm:.0f}mm usable)")
    return out_path


# Internal scheme id (as stored in semester_headings/student_records'
# 'scheme' column, e.g. 'k_scheme') <-> the single-letter scheme code
# used by the seating chart and the global scheme picker (e.g. 'K').
SCHEME_ID_TO_LETTER = {"k_scheme": "K", "i_scheme": "I"}


def _record_scheme_letter(rec):
    """Best-effort scheme LETTER ('K'/'I'/...) for a raw record from
    load_all_records_from_db(). Older/untagged rows (no 'scheme' column
    value) default to 'K', since K-scheme was the only one in use before
    scheme-tagging existed."""
    scheme_id = rec.get("scheme") if hasattr(rec, "get") else None
    return SCHEME_ID_TO_LETTER.get(scheme_id, "K")


def _compute_student_status_full(all_extracted, db_path=DB_FILE):
    """Shared engine behind compute_student_status() and
    compute_student_status_sources() -- the LABELED HYBRID. Internally
    still keyed by (enrollment, semester_label, scheme) while computing,
    because the INFERENCE step genuinely needs per-scheme grouping to
    stay correct (highest semester an enrollment has data for WITHIN
    THAT SCHEME = "Regular", every lower semester within that same
    scheme = "EX") -- a student's K-scheme and I-scheme histories must
    never be mixed together when inferring. The seating chart (MSBTE's
    own Regular/EX answer) is authoritative wherever it exists for that
    triple; only where no seating chart row exists does this fall back
    to the inferred rule.

    NOTE: the seating chart itself is ALWAYS read from SEATING_DB_FILE,
    never from `db_path` -- seating chart data is shared across every
    scheme, not scoped to whichever scheme's operational database
    `db_path` currently points at (see SEATING_DB_FILE's definition).
    `db_path` (the caller's currently-active scheme database) is only
    used below for the inferred-fallback step, which reads
    `all_extracted` -- already loaded by the caller -- not the database
    directly.

    The RETURNED result is then collapsed down to (enrollment,
    semester_label) -- scheme dropped entirely -- since nothing outside
    Seating Chart mode distinguishes scheme any more. A given enrollment
    is expected to have at most one scheme's data for any one
    semester_label in practice, so this collapse is safe; on the rare
    chance of a genuine collision, a chart-sourced answer wins over an
    inferred one.

    Returns: {(enrollment, semester_label): {"status": "Regular"|"EX",
              "source": "chart"|"inferred"}}
    """
    def sem_rank(sem):
        return SEMESTER_NAMES.index(sem) if sem in SEMESTER_NAMES else len(SEMESTER_NAMES)

    by_triple = {}

    # 1) Seating chart -- authoritative wherever present. Always read
    # from the shared SEATING_DB_FILE, never from db_path.
    chart_rows = []
    if os.path.exists(SEATING_DB_FILE):
        conn = sqlite3.connect(SEATING_DB_FILE)
        conn.row_factory = sqlite3.Row
        try:
            chart_rows = conn.execute(
                "SELECT enrollment, semester_label, scheme, status FROM seating_chart"
            ).fetchall()
        except sqlite3.OperationalError:
            chart_rows = []  # table doesn't exist yet
        conn.close()
    for r in chart_rows:
        by_triple[(r["enrollment"], r["semester_label"], r["scheme"])] = {"status": r["status"], "source": "chart"}

    # 2) Inferred fallback -- grouped by (enrollment, scheme), only for
    # triples the seating chart doesn't cover.
    sems_by_enr_scheme = {}
    for r in all_extracted:
        enr = r["enrollment"]
        if not enr:
            continue
        scheme = _record_scheme_letter(r)
        sems_by_enr_scheme.setdefault((enr, scheme), set()).add(r["semester_label"])

    for (enr, scheme), sems in sems_by_enr_scheme.items():
        highest = max(sems, key=sem_rank)
        for sem in sems:
            key = (enr, sem, scheme)
            if key in by_triple:
                continue  # seating chart already answered this one
            by_triple[key] = {
                "status": "Regular" if sem == highest else "EX",
                "source": "inferred",
            }

    # Collapse scheme out of the key -- chart-sourced wins over inferred
    # if the same (enrollment, semester_label) somehow appears under
    # more than one scheme.
    result = {}
    for (enr, sem, _scheme), v in by_triple.items():
        key = (enr, sem)
        existing = result.get(key)
        if existing is None or (existing["source"] == "inferred" and v["source"] == "chart"):
            result[key] = v

    return result


def compute_student_status(all_extracted, db_path=DB_FILE):
    """Classify every (enrollment, semester_label) pair as "Regular" or
    "EX", using MSBTE's own seating chart wherever one has been imported
    (see seating_chart table / the "Seating Chart" mode), and falling
    back to inference only where no seating chart row exists. Scheme is
    not part of this any more -- see _compute_student_status_full().

    Returns: {(enrollment, semester_label): "Regular" | "EX"}
    """
    full = _compute_student_status_full(all_extracted, db_path)
    return {key: v["status"] for key, v in full.items()}


def compute_student_status_sources(all_extracted, db_path=DB_FILE):
    """Companion to compute_student_status() -- same keys, but tells you
    whether each (enrollment, semester_label)'s status came from the
    seating chart ("chart", ground truth) or was guessed ("inferred", no
    seating chart row exists for that pair yet).

    Returns: {(enrollment, semester_label): "chart" | "inferred"}
    """
    full = _compute_student_status_full(all_extracted, db_path)
    return {key: v["source"] for key, v in full.items()}


# Extend here for future MSBTE scheme letters (e.g. a hypothetical
# next scheme "N" -> "n_scheme"). This is the single place the
# semester-scheme cell's letter is translated to an internal scheme id.
SCHEME_LETTER_MAP = {"K": "k_scheme", "I": "i_scheme"}


def parse_semester_scheme_code(raw):
    """Parses MSBTE's composite semester-scheme cell, e.g. "TX-4-K", into
    (semester_label, scheme_letter, error). Format is X-N-S, split on
    '-' from the left:
        segment 1 ("TX")  -- currently unused/pass-through, not validated
        segment 2 ("4")   -- semester number, 1-6
        segment 3 ("K")   -- scheme letter (see SCHEME_LETTER_MAP)

    Returns (semester_label, scheme_letter, None) on success, or
    (None, None, error_message) on failure. scheme_letter is returned
    upper-cased (e.g. "K", "I") -- this is what's stored in the
    seating_chart.scheme column and used as the scheme id everywhere in
    the app (Train/Extract/Report/etc. all key off this same letter).
    """
    text = (raw or "").strip()
    parts = text.split("-")
    if len(parts) < 3:
        return None, None, f"expected 'X-N-S' format (e.g. 'TX-4-K'), found '{raw}'"
    sem_part, scheme_part = parts[1].strip(), parts[2].strip().upper()
    try:
        sem_num = int(float(sem_part))
    except (ValueError, TypeError):
        return None, None, f"semester segment must be a number 1-{len(SEMESTER_NAMES)}, found '{sem_part}'"
    if not (1 <= sem_num <= len(SEMESTER_NAMES)):
        return None, None, f"semester segment must be 1-{len(SEMESTER_NAMES)}, found '{sem_num}'"
    if scheme_part not in SCHEME_LETTER_MAP:
        return None, None, f"unrecognized scheme letter '{scheme_part}' (known: {', '.join(SCHEME_LETTER_MAP)})"
    return SEMESTER_NAMES[sem_num - 1], scheme_part, None


def parse_seating_chart_rows(text):
    """Splits a block of text copy-pasted from MSBTE's seating chart
    Excel into rows of cells -- same tab-separated clipboard mechanics
    as parse_pasted_grid(). Column 4 is still the raw composite
    semester-scheme text (e.g. "TX-4-K") at this point -- it gets split
    into semester_label + scheme in save_seating_chart_rows()."""
    return parse_pasted_grid(text)


def save_seating_chart_rows(rows, db_path=SEATING_DB_FILE):
    """Validates and upserts seating chart rows -- one row per
    (enrollment, semester_label, scheme), REPLACING any existing row for
    that same triple (so re-pasting a corrected row updates it in place
    rather than creating a duplicate or silently being ignored).

    Each row must have exactly 6 cells, in order: Enrollment Number,
    Student Name, Seat Number, Semester-Scheme code (e.g. "TX-4-K"),
    Regular/EX (R or X), Subject Appeared. Column 4 is split here into
    semester_label + scheme via parse_semester_scheme_code().

    Returns (saved_count, errors) -- a row with the wrong cell count, a
    blank/invalid enrollment, an unparseable semester-scheme code, or an
    unrecognized Regular/EX letter is skipped and reported, never
    silently dropped or guessed at.
    """
    init_seating_db(db_path)
    errors = []
    to_save = []  # (enrollment, semester_label, scheme, student_name, seat_number, status, subjects_appeared)

    for r_i, row in enumerate(rows):
        if len(row) < 6:
            errors.append(f"Row {r_i + 1}: expected 6 columns, found {len(row)} -- skipped")
            continue
        enrollment = (row[0] or "").strip()
        student_name = (row[1] or "").strip()
        seat_number = (row[2] or "").strip()
        sem_scheme_raw = (row[3] or "").strip()
        status_raw = (row[4] or "").strip().upper()
        subjects_appeared = (row[5] or "").strip()

        if not enrollment:
            errors.append(f"Row {r_i + 1}: blank Enrollment Number -- skipped")
            continue

        semester_label, scheme, err = parse_semester_scheme_code(sem_scheme_raw)
        if err:
            errors.append(f"Row {r_i + 1}: semester-scheme code '{sem_scheme_raw}' -- {err} -- skipped")
            continue

        if status_raw not in ("R", "X"):
            errors.append(
                f"Row {r_i + 1}: Regular/EX must be 'R' or 'X', found '{row[4]}' -- skipped"
            )
            continue
        status = "Regular" if status_raw == "R" else "EX"

        to_save.append((enrollment, semester_label, scheme, student_name, seat_number, status, subjects_appeared))

    conn = sqlite3.connect(db_path)
    conn.executemany("""
        INSERT INTO seating_chart
            (enrollment, semester_label, scheme, student_name, seat_number, status, subjects_appeared)
        VALUES (?, ?, ?, ?, ?, ?, ?)
        ON CONFLICT(enrollment, semester_label, scheme)
        DO UPDATE SET student_name=excluded.student_name, seat_number=excluded.seat_number,
                      status=excluded.status, subjects_appeared=excluded.subjects_appeared
    """, to_save)
    conn.commit()
    conn.close()

    return len(to_save), errors


def list_active_schemes(db_path=SEATING_DB_FILE):
    """Distinct scheme letters ('K', 'I', ...) currently present in the
    seating chart -- this IS the set that drives the global scheme
    selector checkboxes in app.py and every downstream schemewise mode."""
    if not os.path.exists(db_path):
        return []
    conn = sqlite3.connect(db_path)
    try:
        rows = conn.execute(
            "SELECT DISTINCT scheme FROM seating_chart WHERE scheme IS NOT NULL"
        ).fetchall()
    except sqlite3.OperationalError:
        rows = []
    conn.close()
    return sorted(r[0] for r in rows)


def compute_train_sample_enrollments(scheme, db_path=SEATING_DB_FILE):
    """For ONE scheme, finds the SMALLEST set of enrollment numbers
    (from that scheme's seating chart data) whose combined semester
    coverage spans every semester the scheme actually has -- e.g. if
    enrollment 1234 appears in the seating chart for semesters
    1/2/3/4 and enrollment 5678 appears for 5/6, {1234, 5678} covers
    every semester with just 2 enrollments, so Train mode doesn't need
    a sample per semester, just enough samples to touch every one.

    This is the classic Minimum Set Cover problem (NP-hard exactly),
    solved here with the standard GREEDY approximation: repeatedly pick
    whichever remaining enrollment covers the most still-uncovered
    semesters, until every semester is covered. This doesn't guarantee
    the mathematically smallest possible set in every case, but it's
    the well-known near-optimal, fast, and deterministic approach (ties
    broken by enrollment number, ascending, for reproducibility).

    Returns a list of dicts, in selection order:
        [{"enrollment": "...", "semesters_covered": [...],
          "new_semesters": [...]}, ...]
    where "semesters_covered" is EVERY semester that enrollment has
    seating-chart data for (within this scheme), and "new_semesters" is
    just the subset that wasn't already covered by an earlier pick in
    this list -- i.e. why this enrollment was chosen. Empty list if this
    scheme has no seating chart data.
    """
    conn = sqlite3.connect(db_path)
    conn.row_factory = sqlite3.Row
    try:
        rows = conn.execute(
            "SELECT enrollment, semester_label FROM seating_chart WHERE scheme = ?", (scheme,)
        ).fetchall()
    except sqlite3.OperationalError:
        rows = []
    conn.close()
    if not rows:
        return []

    semesters_by_enr = {}
    for r in rows:
        semesters_by_enr.setdefault(r["enrollment"], set()).add(r["semester_label"])

    all_semesters = set()
    for sems in semesters_by_enr.values():
        all_semesters |= sems

    def sem_rank(sem):
        return SEMESTER_NAMES.index(sem) if sem in SEMESTER_NAMES else len(SEMESTER_NAMES)

    uncovered = set(all_semesters)
    selected = []
    remaining = dict(semesters_by_enr)

    while uncovered and remaining:
        # Pick the enrollment covering the most still-uncovered semesters;
        # tie-break by enrollment number (ascending) for a deterministic,
        # reproducible result across repeated runs on the same data.
        best_enr = min(
            remaining,
            key=lambda enr: (-len(remaining[enr] & uncovered), enr),
        )
        new_sems = remaining[best_enr] & uncovered
        if not new_sems:
            break  # nothing left can cover any more semesters
        selected.append({
            "enrollment": best_enr,
            "semesters_covered": sorted(semesters_by_enr[best_enr], key=sem_rank),
            "new_semesters": sorted(new_sems, key=sem_rank),
        })
        uncovered -= new_sems
        del remaining[best_enr]

    return selected


def wipe_seating_chart_data(db_path=SEATING_DB_FILE):
    """Deletes every row from seating_chart -- a full wipe, independent
    of any other table (student_records, subjectwise_student_records,
    canonical_marks, yearly_gap_flags are all untouched). Returns the
    number of rows deleted."""
    if not os.path.exists(db_path):
        return 0
    conn = sqlite3.connect(db_path)
    count = conn.execute("SELECT COUNT(*) FROM seating_chart").fetchone()[0]
    conn.execute("DELETE FROM seating_chart")
    conn.commit()
    conn.close()
    return count


def delete_result_semesters(enrollment, semester_labels, db_path=DB_FILE):
    """Deletes result data for one enrollment, restricted to the given
    list of semester_label values -- other semesters for the same
    enrollment are left completely untouched. Removes rows from all
    three result tables (student_records, subjectwise_student_records,
    canonical_marks) plus any yearly_gap_flags row that references one
    of the deleted semesters as its present_semester or
    missing_semester (those flags would otherwise point at data that no
    longer exists -- re-run the yearly gap check, or re-import the
    semester via CSV/online train, to regenerate them).

    Deliberately does NOT touch seating_chart -- recheck-mode deletion
    is scoped only to already-trained/extracted/imported result data.

    Returns a dict of per-table deleted row counts."""
    enrollment = (enrollment or "").strip()
    semester_labels = [s for s in (semester_labels or []) if s]
    if not enrollment or not semester_labels or not os.path.exists(db_path):
        return {"student_records": 0, "subjectwise_student_records": 0,
                "canonical_marks": 0, "yearly_gap_flags": 0}

    placeholders = ",".join("?" * len(semester_labels))
    conn = sqlite3.connect(db_path)
    counts = {}
    for table in ("student_records", "subjectwise_student_records", "canonical_marks"):
        cur = conn.execute(
            f"DELETE FROM {table} WHERE enrollment = ? AND semester_label IN ({placeholders})",
            [enrollment, *semester_labels],
        )
        counts[table] = cur.rowcount
    cur = conn.execute(
        f"DELETE FROM yearly_gap_flags WHERE enrollment = ? "
        f"AND (present_semester IN ({placeholders}) OR missing_semester IN ({placeholders}))",
        [enrollment, *semester_labels, *semester_labels],
    )
    counts["yearly_gap_flags"] = cur.rowcount
    conn.commit()
    conn.close()
    return counts


def compute_seating_chart_gap(semester_labels, student_status, present_enrollments):
    """Compares who a report is ABOUT TO SHOW against who the seating
    chart says should exist for that same semester(s)+status scope --
    catching exactly the "56 in the seating chart but only 55 in the
    report" gap: an enrollment the seating chart lists, but for which no
    marks data ever got Trained/Extracted/Offline-imported, so it never
    made it into the report's own student list at all. Scheme is not
    part of this scope any more -- every seating-chart row for this
    semester+status counts, regardless of which scheme it came from.

    Always reads the seating chart from SEATING_DB_FILE -- the shared
    file, never whichever scheme's operational database the caller
    happens to be working against (see SEATING_DB_FILE's definition).
    That's why this function takes no db_path parameter at all.

    semester_labels: list of semester_label strings this report's scope
        covers (usually one; a Yearly-scoped report passes several).
    student_status: "regular" | "ex" | "both" -- same filter the report
        itself is already using.
    present_enrollments: set of enrollment numbers already in the
        report's OWN student list, post status-filter -- i.e. who the
        report would show without this check.

    Returns {"seating_chart_count": int, "report_count": int,
             "missing": [{"enrollment","student_name","seat_number",
             "semester_label","status"}, ...]} -- missing is
    sorted by semester then enrollment, empty if nothing's missing.
    """
    rows = []
    if os.path.exists(SEATING_DB_FILE):
        conn = sqlite3.connect(SEATING_DB_FILE)
        conn.row_factory = sqlite3.Row
        try:
            rows = conn.execute(
                "SELECT enrollment, semester_label, student_name, seat_number, status FROM seating_chart"
            ).fetchall()
        except sqlite3.OperationalError:
            rows = []
        conn.close()

    wanted_statuses = {
        "regular": {"Regular"}, "ex": {"EX"}, "both": {"Regular", "EX"},
    }.get(student_status, {"Regular", "EX"})
    sem_set = set(semester_labels)
    scoped = [r for r in rows if r["semester_label"] in sem_set and r["status"] in wanted_statuses]

    missing = [
        {
            "enrollment": r["enrollment"], "student_name": r["student_name"] or "",
            "seat_number": r["seat_number"] or "", "semester_label": r["semester_label"],
            "status": r["status"],
        }
        for r in scoped if r["enrollment"] not in present_enrollments
    ]
    missing.sort(key=lambda m: (m["semester_label"], m["enrollment"]))

    return {
        "seating_chart_count": len(scoped), "report_count": len(present_enrollments), "missing": missing,
    }


def seating_chart_gap_note_lines(gap):
    """Turns compute_seating_chart_gap()'s result into the 1-2 lines of
    text every report prints for this -- a count line always, and (only
    if something's actually missing) a second line naming exactly which
    enrollment numbers, so the gap is visible both as a number and as a
    concrete, checkable list -- never silently absorbed into a smaller
    total with no explanation.

    Returns [line1] or [line1, line2].
    """
    line1 = (
        f"Total Appeared in Report: {gap['report_count']}  "
        f"(Seating Chart: {gap['seating_chart_count']})"
    )
    if not gap["missing"]:
        return [line1]
    names = ", ".join(m["enrollment"] for m in gap["missing"])
    line2 = (
        f"WARNING: {len(gap['missing'])} student(s) listed in the seating chart have NO marks "
        f"data and are missing from this report's totals: {names}"
    )
    return [line1, line2]


def _report_seating_gap_lines(semester_labels, student_status, db_path=DB_FILE):
    """Self-contained variant of the seating-chart gap check for report
    generators whose row-building helper doesn't hand back its own final
    enrollment list (e.g. K7 Part B/C, Topper List, Bright/Weak, Yearly
    Eligibility/Result). Independently recomputes which enrollments have
    marks data for this semester_labels+status scope, and returns the
    same warning lines seating_chart_gap_note_lines() would.

    semester_labels: a single semester_label string, or a list (for a
    report section spanning more than one semester, e.g. one academic
    year) -- an enrollment counts as "present" for the scope if it
    matches the wanted status in at least one of those semesters.
    """
    if isinstance(semester_labels, str):
        semester_labels = [semester_labels]
    all_extracted, _ = load_all_records_from_db(db_path)
    sem_set = set(semester_labels)
    present_enr = {r["enrollment"] for r in all_extracted if r["semester_label"] in sem_set and r["enrollment"]}
    if student_status in ("regular", "ex"):
        status_map = compute_student_status(all_extracted, db_path)
        wanted = "Regular" if student_status == "regular" else "EX"
        present_enr = {e for e in present_enr if any(status_map.get((e, s)) == wanted for s in semester_labels)}
    gap = compute_seating_chart_gap(semester_labels, student_status, present_enr)
    return seating_chart_gap_note_lines(gap)


def get_seating_chart_summary(db_path=SEATING_DB_FILE):
    """Per-SCHEME semester-wise + grand-total Regular/EX counts (every
    enrollment+semester+scheme row counts separately -- the same student
    appearing in 3 semesters counts 3 times, and a student appearing
    under two different schemes counts once per scheme), plus per-scheme
    per-semester student lists (for the drill-down view) and per-scheme
    sorted UNIQUE enrollment lists (for feeding into that scheme's Train
    mode).

    Returns {"schemes": [scheme, ...], "by_scheme": {scheme: {
        "by_semester": [{"semester_label","regular_count","ex_count",
            "total_count","regular_students","ex_students"}, ...],
        "grand_total": {"regular_count","ex_count","total_count"},
        "unique_enrollments": [enrollment, ...],
    }}}
    Each student entry in regular_students/ex_students is
    {"enrollment","student_name","seat_number"}. Empty ("schemes": [],
    "by_scheme": {}) if no seating chart data exists yet.
    """
    conn = sqlite3.connect(db_path)
    conn.row_factory = sqlite3.Row
    try:
        rows = conn.execute("""
            SELECT enrollment, semester_label, scheme, student_name, seat_number, status
            FROM seating_chart
        """).fetchall()
    except sqlite3.OperationalError:
        rows = []
    conn.close()

    schemes = sorted({r["scheme"] for r in rows if r["scheme"]})
    by_scheme = {}

    for scheme in schemes:
        scheme_rows = [r for r in rows if r["scheme"] == scheme]
        by_sem = {}
        unique_enrollments = set()
        for r in scheme_rows:
            unique_enrollments.add(r["enrollment"])
            sem = r["semester_label"]
            bucket = by_sem.setdefault(sem, {"regular_students": [], "ex_students": []})
            entry = {
                "enrollment": r["enrollment"], "student_name": r["student_name"] or "",
                "seat_number": r["seat_number"] or "",
            }
            if r["status"] == "Regular":
                bucket["regular_students"].append(entry)
            else:
                bucket["ex_students"].append(entry)

        by_semester = []
        grand_regular = grand_ex = 0
        for sem in SEMESTER_NAMES:
            if sem not in by_sem:
                continue
            regular_students = sorted(by_sem[sem]["regular_students"], key=lambda x: x["enrollment"])
            ex_students = sorted(by_sem[sem]["ex_students"], key=lambda x: x["enrollment"])
            regular_count = len(regular_students)
            ex_count = len(ex_students)
            grand_regular += regular_count
            grand_ex += ex_count
            by_semester.append({
                "semester_label": sem, "regular_count": regular_count, "ex_count": ex_count,
                "total_count": regular_count + ex_count,
                "regular_students": regular_students, "ex_students": ex_students,
            })

        by_scheme[scheme] = {
            "by_semester": by_semester,
            "grand_total": {
                "regular_count": grand_regular, "ex_count": grand_ex,
                "total_count": grand_regular + grand_ex,
            },
            "unique_enrollments": sorted(unique_enrollments),
        }

    return {"schemes": schemes, "by_scheme": by_scheme}


def build_student_history(all_extracted, db_path=DB_FILE):
    """Reshape flat records into the per-(enrollment, semester) shape the
    Yearly Result report needs. Reads by group_name/enrollment/semester_label/
    abs_row only -- no cell addresses -- same DB-portability property as
    the rest of the report logic.

    Returns:
      enrollments: sorted list of unique enrollment numbers
      programs_by_enr: enrollment -> program value (its "program" group
        text, taken from whichever of that student's semesters has it --
        it's expected to be the same diploma program across all of a
        student's semesters, so the first one found is used)
      names_by_enr: enrollment -> student name, same "first semester that
        has it" logic as programs_by_enr (its "name" group text)
      semesters: unique semester labels seen across ALL students, ordered
        like the semester-wise report (SEMESTER_NAMES order, then
        anything unrecognized appended alphabetically)
      history: (enrollment, semester_label) -> {"total_marks",
        "obtained_total_marks", "percentage", "result", "failed_subjects"}
        -- only present for (enrollment, semester_label) pairs the student
        actually has data for, so the report can tell "0 failures" apart
        from "never sat this semester" (blank). "percentage" falls back to
        Obtained/Total*100 (see compute_percentage_fallback()) whenever
        the trained Percentage field itself came back blank but Total
        Marks and Obtained Total Marks are both present -- otherwise a
        missing Percentage would silently skew year-average-marks.
    """
    student_records = [r for r in all_extracted if r["enrollment"]]

    # (enrollment, semester_label) -> {group_name: {field_name: value}}
    by_enr_sem_group = {}
    for r in student_records:
        key = (r["enrollment"], r["semester_label"])
        by_enr_sem_group.setdefault(key, {}).setdefault(
            r["group_name"], {})[r["field_name"]] = r["value"]

    # (enrollment, semester_label) -> set of DISTINCT failed subjects
    # (one entry per subject, even if it failed on more than one
    # component column -- same "count subjects, not starred cells" rule
    # as count_failed_subjects()). Old flat system: keyed by abs_row.
    failed_index = {}
    for r in student_records:
        if r["group_name"] == "obtained_marks" and r["value"] and "*" in str(r["value"]):
            key = (r["enrollment"], r["semester_label"])
            failed_index.setdefault(key, set()).add(("row", r["abs_row"]))

    # A semester trained through the newer subject/level/component tree
    # trainer (Train mode Steps 1-6) stores its marks in
    # subjectwise_student_records instead of student_records -- add THOSE
    # failures too, one entry per distinct subject_index, so Yearly
    # Result/Eligibility/Topper Lists don't silently show 0 failures for
    # every such semester. A blank/dropped column never carries a '*', so
    # it's naturally excluded here without any extra filtering.
    if os.path.exists(db_path):
        conn = sqlite3.connect(db_path)
        try:
            subj_rows = conn.execute(
                "SELECT enrollment, semester_label, subject_index, value "
                "FROM subjectwise_student_records WHERE role = 'obtained'"
            ).fetchall()
        except sqlite3.OperationalError:
            subj_rows = []
        conn.close()
        for enr, sem, subject_index, value in subj_rows:
            if value and "*" in str(value):
                key = (enr, sem)
                failed_index.setdefault(key, set()).add(("subj", subject_index))

    def group_text(fields_by_name):
        if not fields_by_name:
            return ""
        return " ".join(clean_value(fields_by_name[k]) for k in sorted(fields_by_name))

    enrollments = sorted({enr for enr, _ in by_enr_sem_group})
    semesters = sorted({sem for _, sem in by_enr_sem_group},
                        key=lambda s: SEMESTER_NAMES.index(s) if s in SEMESTER_NAMES else 999)

    def first_available(group_name):
        """enrollment -> that group's text, taken from whichever of the
        student's semesters has it first (in semester order) -- for
        identity facts expected constant across a student's whole
        history, like program or name."""
        out = {}
        for enr in enrollments:
            value = ""
            for sem in semesters:
                groups = by_enr_sem_group.get((enr, sem), {})
                if groups.get(group_name):
                    value = group_text(groups[group_name])
                    break
            out[enr] = value
        return out

    programs_by_enr = first_available("program")
    names_by_enr = first_available("name")

    history = {}
    for (enr, sem), groups in by_enr_sem_group.items():
        total_marks = group_text(groups.get("total_marks", {}))
        obtained_total_marks = group_text(groups.get("obtained_total_marks", {}))
        percentage = group_text(groups.get("percentage", {}))
        if not percentage:
            computed = compute_percentage_fallback(total_marks, obtained_total_marks)
            if computed is not None:
                percentage = computed
        history[(enr, sem)] = {
            "total_marks": total_marks,
            "obtained_total_marks": obtained_total_marks,
            "percentage": percentage,
            "result": group_text(groups.get("result", {})),
            "failed_subjects": len(failed_index.get((enr, sem), set())),
        }

    return enrollments, programs_by_enr, names_by_enr, semesters, history


def compute_subject_count_by_semester(db_path=DB_FILE):
    """{semester_label: subject_count} -- a curriculum fact (same for
    every student in that semester), used by the Yearly Result/
    Eligibility reports' "Total Sum of Subjects" column. Merges BOTH
    sources: the old flat 'subjects' heading group (semester_headings
    table) for a semester trained the old way, and the newer `subjects`
    table for one trained through the tree trainer -- a given semester
    only ever has data in one or the other, never both, so there's no
    double-counting risk."""
    counts = {}
    conn = sqlite3.connect(db_path)
    try:
        rows = conn.execute(
            "SELECT semester_label, abs_row FROM semester_headings WHERE group_name = 'subjects'"
        ).fetchall()
    except sqlite3.OperationalError:
        rows = []
    conn.close()
    by_sem_rows = {}
    for sem, abs_row in rows:
        by_sem_rows.setdefault(sem, set()).add(abs_row)
    for sem, rws in by_sem_rows.items():
        counts[sem] = len(rws)
    for sem in list_subjectwise_semesters(db_path):
        n = len(load_subjects(sem, db_path))
        if n:
            counts[sem] = n
    return counts


def compute_yearly_semester_gaps(db_path=DB_FILE):
    """Find every enrollment that has data for exactly ONE semester of a
    YEAR_GROUPS pair but not the other -- e.g. Second Semester marks are
    in the database but that same enrollment's First Semester marks were
    never extracted. This is deliberately different from an enrollment
    that simply hasn't reached that year yet (ZERO semesters of the pair
    -- not a gap, business as usual) or one that already has both
    semesters (complete -- not a gap either).

    Both Yearly_Result_Report and Yearly_Eligible_NonEligible_Report
    compute a year's figures from "whichever semester(s) of the pair the
    enrollment has data for" -- which is correct for the "hasn't reached
    it yet" case but silently WRONG for this case, since the year's true
    figures need both semesters and one of them just happens to be
    missing from this particular database.

    IMPORTANT -- direction matters: semesters happen in sequence, so a
    student can only ever reach Second Semester after having sat First
    Semester. That means:
      - LATER semester present, EARLIER semester absent -- impossible in
        the real world, so this can only mean the earlier semester's
        data simply never made it into this database. FLAGGED.
      - EARLIER semester present, LATER semester absent -- completely
        normal (the student just hasn't reached the later semester yet,
        or its result isn't out yet). This is exactly the case
        build_student_history()/generate_yearly_result_pdf() already
        handle correctly on purpose (a First Semester-only student still
        gets a partial First Year row). NOT flagged.

    Returns a list of dicts, one per gap found:
        {"enrollment", "year_label", "present_semester", "missing_semester"}
    sorted by academic-year order (First/Second/Final Year) then
    enrollment. See fill_yearly_gaps_from_secondary_db() for how a gap
    gets resolved.
    """
    all_extracted, _all_review = load_all_records_from_db(db_path)
    enrollments, _programs, _names, _semesters, history = build_student_history(all_extracted, db_path)

    year_order = [year_label for year_label, _ in YEAR_GROUPS]
    gaps = []
    for year_label, sems_in_year in YEAR_GROUPS:
        if len(sems_in_year) != 2:
            continue  # only well-defined for a two-semester pair
        earlier_sem, later_sem = sems_in_year  # YEAR_GROUPS lists each pair in chronological order
        for enr in enrollments:
            has_earlier = (enr, earlier_sem) in history
            has_later = (enr, later_sem) in history
            if has_later and not has_earlier:
                gaps.append({"enrollment": enr, "year_label": year_label,
                             "present_semester": later_sem, "missing_semester": earlier_sem})

    gaps.sort(key=lambda g: (year_order.index(g["year_label"]), g["enrollment"]))
    return gaps


def save_yearly_gap_flags_to_db(gaps, db_path=DB_FILE):
    """Stores the result of the latest gap Check as its own group in the
    database (the `yearly_gap_flags` table), replacing whatever was
    stored from a previous Check -- this is a snapshot of "as of right
    now", not accumulating history. Also records that a Check has been
    run at all (see yearly_reports_are_blocked()): the two yearly
    reports stay blocked until the very first Check, and a Check that
    finds zero gaps unblocks them from then on."""
    init_db(db_path)
    conn = sqlite3.connect(db_path)
    conn.execute("DELETE FROM yearly_gap_flags")
    conn.executemany("""
        INSERT INTO yearly_gap_flags (enrollment, year_label, present_semester, missing_semester)
        VALUES (?, ?, ?, ?)
        ON CONFLICT(enrollment, missing_semester) DO UPDATE SET
            year_label=excluded.year_label, present_semester=excluded.present_semester
    """, [(g["enrollment"], g["year_label"], g["present_semester"], g["missing_semester"]) for g in gaps])
    conn.execute("""
        INSERT INTO report_settings (key, value) VALUES ('yearly_gap_checked', '1')
        ON CONFLICT(key) DO UPDATE SET value=excluded.value
    """)
    conn.commit()
    conn.close()


def load_yearly_gap_flags_from_db(db_path=DB_FILE):
    """Whatever's currently on record from the last Check -- same shape
    as compute_yearly_semester_gaps()'s return value."""
    if not os.path.exists(db_path):
        return []
    conn = sqlite3.connect(db_path)
    conn.row_factory = sqlite3.Row
    try:
        rows = [dict(r) for r in conn.execute(
            "SELECT enrollment, year_label, present_semester, missing_semester FROM yearly_gap_flags"
        )]
    except sqlite3.OperationalError:
        rows = []
    conn.close()
    year_order = [year_label for year_label, _ in YEAR_GROUPS]
    rows.sort(key=lambda g: (
        year_order.index(g["year_label"]) if g["year_label"] in year_order else 999,
        g["enrollment"]))
    return rows


def yearly_reports_are_blocked(db_path=DB_FILE):
    """Whether Yearly_Result_Report / Yearly_Eligible_NonEligible_Report
    should be refused right now, and why.

    Returns (blocked: bool, status: str) where status is one of:
      "not_checked" -- a Gap Check has never been run against this
        database (or it's a brand new database) -- blocked.
      "gaps"        -- the last Check found missing-semester gaps that
        haven't all been resolved yet -- blocked.
      "clean"       -- the last Check found zero gaps -- not blocked.

    Note this reflects the database as of the LAST Check, not a live
    recheck -- if you extract more enrollments afterwards, re-run the
    Check (compute_yearly_semester_gaps + save_yearly_gap_flags_to_db)
    so this stays accurate.
    """
    settings = load_report_settings(db_path)
    if settings.get("yearly_gap_checked") != "1":
        return True, "not_checked"
    gaps = load_yearly_gap_flags_from_db(db_path)
    return (len(gaps) > 0), ("gaps" if gaps else "clean")


def generate_yearly_gap_report_pdf(db_path=DB_FILE, out_path=None):
    """Builds "Yearly_Semester_Gap_List.pdf" from whatever's currently
    stored in `yearly_gap_flags` (i.e. the result of the last Check) --
    Sr.No. / Enrollment No. / Semester, where Semester is the MISSING
    semester that still needs filling in before Yearly_Result_Report or
    Yearly_Eligible_NonEligible_Report can be trusted. Returns None (and
    prints a message) if the last Check found no gaps -- nothing to list.
    """
    from reportlab.lib.pagesizes import A4
    from reportlab.platypus import SimpleDocTemplate, Table, TableStyle, Paragraph, Spacer
    from reportlab.lib.styles import getSampleStyleSheet
    from reportlab.lib.enums import TA_CENTER
    from reportlab.lib import colors
    from reportlab.lib.units import mm

    gaps = load_yearly_gap_flags_from_db(db_path)
    if not gaps:
        print("No missing-semester gaps on record -- run a Gap Check first (or none were found).")
        return None

    out_path = out_path or "Yearly_Semester_Gap_List.pdf"
    styles = getSampleStyleSheet()
    title_style = styles["Heading2"]
    title_style.alignment = TA_CENTER

    story = [
        Paragraph("Missing Semester Data -- Yearly Report Gap List", title_style),
        Spacer(1, 4 * mm),
        Paragraph(
            "These enrollments have data for only one semester of an academic year. "
            "Yearly_Result_Report and Yearly_Eligible_NonEligible_Report cannot be "
            "trusted for them until the semester listed below is filled in.",
            styles["Normal"],
        ),
        Spacer(1, 6 * mm),
    ]

    data = [["Sr.No.", "Enrollment No.", "Semester"]]
    for i, g in enumerate(gaps, start=1):
        data.append([str(i), g["enrollment"], g["missing_semester"].title()])

    table = Table(data, colWidths=[20 * mm, 60 * mm, 70 * mm], repeatRows=1)
    table.setStyle(TableStyle([
        ("GRID", (0, 0), (-1, -1), 0.5, colors.black),
        ("BACKGROUND", (0, 0), (-1, 0), colors.HexColor("#d9d9d9")),
        ("FONTNAME", (0, 0), (-1, 0), "Helvetica-Bold"),
        ("ALIGN", (0, 0), (-1, -1), "CENTER"),
        ("FONTSIZE", (0, 0), (-1, -1), 9),
        ("VALIGN", (0, 0), (-1, -1), "MIDDLE"),
    ]))
    story.append(table)

    doc = SimpleDocTemplate(out_path, pagesize=A4)
    doc.build(story)
    print(f"Saved {out_path}")
    return out_path


def check_yearly_gap_matches(secondary_db_path, db_path=DB_FILE):
    """READ-ONLY preview -- does not modify either database. Live-
    recomputes the current gaps (compute_yearly_semester_gaps()), then
    for each one checks whether the secondary database actually has
    matching student_records rows for that (enrollment, missing_semester)
    -- so the person can see, visually, which gaps this file will
    resolve and which it won't, BEFORE anything gets written.

    Returns a list of dicts, one per current gap:
        {"enrollment", "year_label", "present_semester",
         "missing_semester", "found": True/False}
    Same order as compute_yearly_semester_gaps(). If there are no gaps
    right now, returns [].
    """
    gaps = compute_yearly_semester_gaps(db_path)
    if not gaps:
        return []
    if not os.path.exists(secondary_db_path):
        return [dict(g, found=False) for g in gaps]

    src = sqlite3.connect(secondary_db_path)
    results = []
    for g in gaps:
        try:
            count = src.execute(
                "SELECT COUNT(*) FROM student_records WHERE enrollment = ? AND semester_label = ?",
                (g["enrollment"], g["missing_semester"]),
            ).fetchone()[0]
        except sqlite3.OperationalError:
            count = 0
        results.append({**g, "found": count > 0})
    src.close()
    return results


def fill_yearly_gaps_from_secondary_db(secondary_db_path, db_path=DB_FILE):
    """Reads the (enrollment, missing_semester) pairs found by a LIVE
    recomputation of compute_yearly_semester_gaps() (not whatever's
    stored in `yearly_gap_flags` from the last Check -- see note below)
    out of a SEPARATE database file -- e.g. one extracted on another
    machine, or an older backup that happens to have the semester this
    database is missing -- and upserts just those rows into THIS
    database's student_records (same ON CONFLICT upsert save_records_to_db()
    already uses, so calling this more than once is always safe). Also
    copies that semester's semester_headings (subjects/THPRSLA/FASA/
    maximum marks) over from the secondary database if this database
    doesn't have them for that semester yet -- needed for Total Sum of
    Subjects and other curriculum-level figures to compute correctly
    once the gap is filled.

    Does NOT touch any enrollment/semester that isn't currently a gap,
    and does NOT merge anything else from the secondary database.

    Deliberately recomputes live rather than trusting `yearly_gap_flags`:
    if the database changed since the last Check (a fresh Extract, an
    Erase, etc.) the stored flags can be stale or empty, which used to
    make this silently fill nothing -- recomputing here means Upload
    always works off the database's actual current state, regardless of
    whether Check happens to have been (re-)run since.

    Returns {"filled": [...gaps found & copied...], "still_missing":
    [...gaps NOT found in the secondary database either...]}. After
    calling this, re-run compute_yearly_semester_gaps() and
    save_yearly_gap_flags_to_db() to refresh what's on record -- entries
    in "still_missing" should remain flagged.
    """
    flagged = compute_yearly_semester_gaps(db_path)
    if not flagged:
        return {"filled": [], "still_missing": []}
    if not os.path.exists(secondary_db_path):
        return {"filled": [], "still_missing": flagged}

    init_db(db_path)
    src = sqlite3.connect(secondary_db_path)
    src.row_factory = sqlite3.Row
    dest = sqlite3.connect(db_path)

    existing_heading_sems = {row[0] for row in dest.execute(
        "SELECT DISTINCT semester_label FROM semester_headings")}
    copied_heading_sems = set()

    filled, still_missing = [], []
    for gap in flagged:
        enr, sem = gap["enrollment"], gap["missing_semester"]
        rows = src.execute(
            "SELECT * FROM student_records WHERE enrollment = ? AND semester_label = ?",
            (enr, sem),
        ).fetchall()
        if not rows:
            still_missing.append(gap)
            continue

        dest.executemany("""
            INSERT INTO student_records
                (enrollment, semester_label, group_name, field_name,
                 range_idx, row_offset, col_offset, abs_row, abs_col, value)
            VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
            ON CONFLICT(enrollment, semester_label, group_name, abs_row, abs_col)
            DO UPDATE SET field_name=excluded.field_name, value=excluded.value
        """, [
            (r["enrollment"], r["semester_label"], r["group_name"], r["field_name"],
             r["range_idx"], r["row_offset"], r["col_offset"], r["abs_row"], r["abs_col"], r["value"])
            for r in rows
        ])

        if sem not in existing_heading_sems and sem not in copied_heading_sems:
            try:
                heading_rows = src.execute(
                    "SELECT * FROM semester_headings WHERE semester_label = ?", (sem,)
                ).fetchall()
            except sqlite3.OperationalError:
                heading_rows = []
            if heading_rows:
                dest.executemany("""
                    INSERT INTO semester_headings
                        (semester_label, group_name, field_name, range_idx, row_offset, col_offset, abs_row, abs_col, value)
                    VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)
                    ON CONFLICT(semester_label, group_name, abs_row, abs_col)
                    DO UPDATE SET field_name=excluded.field_name, value=excluded.value
                """, [
                    (r["semester_label"], r["group_name"], r["field_name"], r["range_idx"],
                     r["row_offset"], r["col_offset"], r["abs_row"], r["abs_col"], r["value"])
                    for r in heading_rows
                ])
            copied_heading_sems.add(sem)

        filled.append(gap)

    dest.commit()
    dest.close()
    src.close()
    return {"filled": filled, "still_missing": still_missing}


def generate_yearly_result_pdf(db_path=DB_FILE, out_path=None, student_status="both",
                                include_yearly_block=True):
    """Build the cross-semester "Yearly Result" report: the report
    heading block first ("Yearly result" / Institute Name+Address /
    Program / Academic Year / Exam Session -- see
    build_yearly_result_heading_flowables() -- using whichever semester is the
    LATEST one found in the database, since this report spans every
    semester at once and there's no single "this semester" otherwise),
    then one SECTION per academic year (First Year, Second Year, Final
    Year), each starting on its own page(s), then the signature block
    once at the very end (see build_report_end_flowables()) -- read
    straight from the database. No Excel involved anywhere in this path.

    student_status: "both" (default), "regular", or "ex" -- filters which
    enrollments appear in each year's section based on
    compute_student_status(): an enrollment only appears in a given
    section if it has at least one semester within that section matching
    the requested status ("regular" = that semester is its highest
    semester reached anywhere in the database; "ex" = it has since moved
    on to a higher semester than that one).

    Per-year section:
      - Columns: Sr.No. | Enrollment No | Name of Student | Program |
                 <that year's semester(s), 5 columns each: Total Marks /
                 Obtained Total / Percentage / Result / Failed Subjects> |
                 <that year's block, 5 columns: Failed Count / Average
                 Marks / Total Sum of Subjects / Eligible/Non-Eligible
                 for Next Year / Remark>
      - Rows: ONLY enrollment numbers that actually have data for one of
        that year's semesters -- a student who never reached Third/Fourth
        Semester simply doesn't get a row in the Second Year section, so
        each section is a clean, self-contained sheet for that year
        rather than one giant table with blank rows for years a student
        hasn't reached. Sr.No. restarts at 1 within each section.
      - Every column is centre-aligned except Name of Student and
        Program, which stay left-aligned since they hold longer
        free-text.

    A student's failed-subject count for a semester is the number of
    DISTINCT subjects with an asterisk anywhere in obtained_marks for that
    (enrollment, semester) -- same rule as the semester-wise report's
    count_failed_subjects().

    Each year's block covers its semester pair (e.g. First Semester +
    Second Semester):
      - Failed Count: sum of the failed-subject counts of whichever
        semester(s) in the pair the enrollment actually has data for --
        so a student only through Semester 1 still gets a partial count
        from Semester 1 alone, rather than a blank, until Semester 2's
        data lands.
      - Average Marks: average of the Percentage values of whichever
        semester(s) in the pair the enrollment has data for.
      - Total Sum of Subjects: the semester-wide subject COUNT (from the
        "subjects" heading group, same for every student in a given
        semester) summed across whichever semester(s) in the pair have
        subject data trained -- this is a curriculum fact, not a
        per-student one, so it's the same value down the whole column.
      - Eligible/Non-Eligible for Next Year -- TWO rules, applied together:
          Rule 1: compares the year's own Failed Count against the
          maximum allowed failures for that year's Total Sum of Subjects
          (max_allowed_failed_for_eligibility() -- roughly one extra
          allowed failure per 3 additional subjects). Blank if either
          the failed count or the subject total isn't available yet.
          Rule 2: even where Rule 1 says Eligible, an enrollment that
          still has any unresolved failures in the immediately LOWER
          year (that year's own Failed Count > 0) is forced to Not
          Eligible for THIS higher year instead -- e.g. an enrollment
          that's reached Third/Fourth Semester (so it gets a Second Year
          row) but still has a failed subject sitting in First Year is
          flagged rather than shown as cleanly Eligible for Second Year.
      - Remark: "Lower Semester Pending" whenever Rule 2 above is what
        forced Not Eligible for this year; blank otherwise (including
        for First Year, which has no lower year to check).
    A year section is only included at all if at least one of its two
    semesters appears anywhere in the database. Any semester that doesn't
    fall into a recognized year pair (an unrecognized/custom label) gets
    its own trailing "Other Semesters" section rather than being dropped.

    include_yearly_block=False switches to a SIMPLER report layout: just
    the semester-pair tables side by side, using whatever semesters
    already exist in the database (however incomplete a year is) -- the
    aggregated year block (Failed Count / Average Marks / Total Sum of
    Subjects / Eligible-Non-Eligible / Remark) is left OUT of the layout
    entirely, not blanked. No Gap Check / secondary-database upload is
    needed or expected for this mode -- see yearly_reports_are_blocked(),
    which the caller should skip enforcing when this is False.

    Within a section, if its columns don't all fit legibly on one page
    width, it's further split into however many page-groups are needed
    (Sr.No./Enrollment No./Name/Program repeated on each so every page is
    self-contained) -- a semester's or year's block of columns is never
    split across two page-groups. Landscape A4 throughout.
    """
    from reportlab.lib.pagesizes import A4, landscape
    from reportlab.platypus import SimpleDocTemplate, Table, TableStyle, Paragraph, Spacer, PageBreak
    from reportlab.lib.styles import getSampleStyleSheet
    from reportlab.lib.enums import TA_CENTER, TA_LEFT
    from reportlab.lib import colors
    from reportlab.lib.units import mm

    all_extracted, all_review = load_all_records_from_db(db_path)
    enrollments, programs_by_enr, names_by_enr, semesters, history = build_student_history(all_extracted, db_path)
    if not enrollments:
        print(f"{db_path} has no student data yet. Run 'extract' mode at least once first.")
        return None
    if not semesters:
        print(f"{db_path} has student identity data but no semester summary data "
              f"(Total Marks/Obtained Total/Percentage/Result) yet -- nothing to build a history from.")
        return None

    status_map = compute_student_status(all_extracted, db_path)

    SUB_LABELS = ["Total Marks", "Obtained Total", "Percentage", "Result", "Failed Subjects"]
    SUB_KEYS = ["total_marks", "obtained_total_marks", "percentage", "result", "failed_subjects"]

    # Semester-wide subject counts (constant per semester, same for every
    # student) -- see compute_subject_count_by_semester() for both the old
    # flat-heading source and the newer subjects-table source it merges.
    subject_count_by_sem = compute_subject_count_by_semester(db_path)

    YEAR_SUB_LABELS = ["Failed Count", "Average Marks", "Total Sum of Subjects",
                        "Eligible/Non-Eligible for Next Year", "Remark"]

    semesters_present = set(semesters)
    active_year_groups = [(prefix, sems) for prefix, sems in YEAR_GROUPS
                           if any(s in semesters_present for s in sems)]
    # Rule 2 needs "the immediately lower year" for a given year -- this
    # maps a year's prefix to its position in active_year_groups, so
    # index-1 is that lower year (First Year has no lower year at all).
    year_position = {prefix: i for i, (prefix, _) in enumerate(active_year_groups)}

    def year_failed_count(enr, sems_in_year):
        recs = [history[(enr, s)] for s in sems_in_year if (enr, s) in history]
        if not recs:
            return ""
        return sum(r["failed_subjects"] for r in recs)

    def year_average_marks(enr, sems_in_year):
        values = []
        for s in sems_in_year:
            rec = history.get((enr, s))
            if rec and rec["percentage"] not in ("", None):
                try:
                    values.append(float(str(rec["percentage"]).strip()))
                except ValueError:
                    pass
        if not values:
            return ""
        return round(sum(values) / len(values), 2)

    def year_total_subjects(sems_in_year):
        # A curriculum fact (same for every student), not per-enrollment --
        # blank only if NEITHER semester in the pair has subject data
        # trained yet; otherwise sums whichever semester(s) do.
        present = [subject_count_by_sem[s] for s in sems_in_year if s in subject_count_by_sem]
        if not present:
            return ""
        return sum(present)

    def year_eligibility(enr, prefix, failed_count, total_subjects):
        """Looks up the immediately lower year's own Failed Count (if
        any), then delegates the actual Rule 1 + Rule 2 decision to
        compute_year_eligibility_and_remark() -- shared with the Yearly
        Eligible/Non-Eligible Student List so the two reports agree.
        Returns (eligibility, remark).
        """
        idx = year_position.get(prefix)
        lower_failed = ""
        if idx is not None and idx > 0:
            _, lower_sems = active_year_groups[idx - 1]
            lower_failed = year_failed_count(enr, lower_sems)
        return compute_year_eligibility_and_remark(failed_count, total_subjects, lower_failed)

    # Total subjects is the same value for every row in a given year, so
    # it's computed once per active year group up front.
    total_subjects_by_year = {prefix: year_total_subjects(sems) for prefix, sems in active_year_groups}

    def semester_block(sem):
        return {"label": sem.title(), "sub_labels": SUB_LABELS, "n_cols": 5, "kind": "semester", "sem": sem}

    def year_block(prefix, sems_in_year):
        return {"label": prefix, "sub_labels": YEAR_SUB_LABELS, "n_cols": 5,
                "kind": "year", "prefix": prefix, "sems": sems_in_year}

    def block_row_values(block, enr):
        if block["kind"] == "semester":
            rec = history.get((enr, block["sem"]))
            return [rec[key] if rec else "" for key in SUB_KEYS]
        failed = year_failed_count(enr, block["sems"])
        avg = year_average_marks(enr, block["sems"])
        total_subj = total_subjects_by_year[block["prefix"]]
        eligibility, remark = year_eligibility(enr, block["prefix"], failed, total_subj)
        return [failed, avg, total_subj, eligibility, remark]

    def enrollments_touching(sems):
        """Enrollment numbers (in overall sorted order) that have data
        for at least one of the given semesters -- and, if a status
        filter is active, at least one of those semesters matching the
        requested Regular/EX status."""
        wanted = {"regular": "Regular", "ex": "EX"}.get(student_status)
        touching = set()
        for enr, sem in history:
            if sem not in sems:
                continue
            if wanted is not None and status_map.get((enr, sem)) != wanted:
                continue
            touching.add(enr)
        return [enr for enr in enrollments if enr in touching]

    # An enrollment that's reached a higher year (e.g. has Third/Fourth
    # Semester data, so it belongs in Second Year) is shown ONLY in that
    # highest year's section -- not repeated in First Year too. This is
    # each enrollment's highest active year INDEX (into active_year_groups).
    def highest_year_index(enr):
        highest = None
        for i, (_, sems) in enumerate(active_year_groups):
            if any((enr, s) in history for s in sems):
                highest = i
        return highest

    highest_year_by_enr = {enr: highest_year_index(enr) for enr in enrollments}

    # --- Split the whole report into one SECTION per academic year, each
    # covering just its own semester pair + year block, and only the
    # enrollments that actually have data for that year AND for whom this
    # is their HIGHEST year reached so far -- rather than one giant table
    # with blank rows for years a student hasn't reached yet, or the same
    # enrollment repeated in every lower year it's since moved past. Any
    # semester that doesn't fall into a recognized year pair
    # (unrecognized/custom label) gets its own trailing section instead
    # of silently being dropped. ---
    sections = []
    covered_semesters = set()
    for year_idx, (prefix, sems_in_year) in enumerate(active_year_groups):
        sems_in_data = [s for s in sems_in_year if s in semesters_present]
        covered_semesters.update(sems_in_data)
        blocks = [semester_block(s) for s in sems_in_data]
        if include_yearly_block:
            blocks.append(year_block(prefix, sems_in_year))
        section_enrollments = [enr for enr in enrollments_touching(sems_in_data)
                                if highest_year_by_enr.get(enr) == year_idx]
        sections.append({"title": prefix, "blocks": blocks, "enrollments": section_enrollments,
                          "semesters": sems_in_data})

    leftover_semesters = [s for s in semesters if s not in covered_semesters]
    if leftover_semesters:
        blocks = [semester_block(s) for s in leftover_semesters]
        sections.append({"title": "Other Semesters", "blocks": blocks,
                          "enrollments": enrollments_touching(leftover_semesters),
                          "semesters": leftover_semesters})

    page_size = landscape(A4)
    margin_mm = 4
    usable_w_mm = 297 - 2 * margin_mm

    # --- Fixed identity columns (repeated on every page-group). ---
    srno_w, enroll_w, name_w, program_w = 10.0, 20.0, 26.0, 26.0
    fixed_total = srno_w + enroll_w + name_w + program_w
    avail_flex_w = usable_w_mm - fixed_total

    # --- Pack a section's blocks into page-groups: aim for a legible
    # ~16mm per sub-column, and start a new page-group rather than
    # shrinking below a hard floor. A single block's own columns are
    # still never split across page-groups even in the rare case they
    # alone don't fit -- same "columns never split" guarantee the
    # semester-wise report makes for a single semester's subject columns.
    TARGET_COL_W = 16.0  # mm
    MIN_COL_W = 8.0  # mm -- below this, font/legibility suffers too much
    max_cols_per_page = max(1, int(avail_flex_w // TARGET_COL_W))

    def pack_into_page_groups(blocks):
        # A year section is naturally small (at most 2 semesters + 1 year
        # block = 14 columns), so it almost always fits comfortably on
        # one page even below the "target" width -- keep it as ONE
        # page-group whenever it fits at all down to the minimum legible
        # width, rather than always splitting at the more generous target
        # width. Only fall back to multi-page-group packing (e.g. for an
        # unusually large "Other Semesters" leftover section) if it
        # genuinely doesn't fit even at the floor.
        total_cols = sum(b["n_cols"] for b in blocks)
        if total_cols and total_cols * MIN_COL_W <= avail_flex_w:
            return [blocks]
        page_groups, current, current_cols = [], [], 0
        for block in blocks:
            if current and current_cols + block["n_cols"] > max_cols_per_page:
                page_groups.append(current)
                current, current_cols = [], 0
            current.append(block)
            current_cols += block["n_cols"]
        if current:
            page_groups.append(current)
        return page_groups

    styles = getSampleStyleSheet()

    status_suffix = {"regular": " (Regular)", "ex": " (EX)", "both": ""}.get(student_status, "")
    out_path = out_path or f"Yearly_Result_Report{status_suffix}.pdf"
    doc = SimpleDocTemplate(out_path, pagesize=page_size,
                             leftMargin=margin_mm * mm, rightMargin=margin_mm * mm,
                             topMargin=margin_mm * mm, bottomMargin=margin_mm * mm)
    # Program/Academic Year/Exam Session in the heading represent the
    # LATEST semester found in the database -- the History report spans
    # every semester at once, so there's no single "this semester" to
    # anchor those fields to; the most recent one is the most relevant.
    latest_semester = sorted(semesters, key=lambda s: SEMESTER_NAMES.index(s) if s in SEMESTER_NAMES else 999)[-1]
    story = build_yearly_result_heading_flowables(latest_semester, db_path)
    if not include_yearly_block:
        note_style = styles["Normal"].clone("noyearlyblock")
        note_style.fontSize = 8
        note_style.alignment = TA_CENTER
        story.append(Paragraph(
            "(Semester-pair summary only -- yearly aggregate/eligibility columns not "
            "included; no missing-semester Gap Check was required for this report)",
            note_style,
        ))
        story.append(Spacer(1, 4))

    section_summaries = []
    for si, section in enumerate(sections):
        page_groups = pack_into_page_groups(section["blocks"])
        section_enrollments = section["enrollments"]

        if si > 0:
            story.append(PageBreak())
        story.append(Paragraph(section["title"], styles["Heading3"]))
        gap_style = styles["Normal"].clone(f"yrgap{si}")
        gap_style.fontSize = 8
        gap_warn_style = gap_style.clone(f"yrgapwarn{si}")
        gap_warn_style.textColor = colors.HexColor("#B30000")
        if section["semesters"]:
            for i, line in enumerate(_report_seating_gap_lines(section["semesters"], student_status, db_path)):
                story.append(Paragraph(line, gap_warn_style if i > 0 else gap_style))
        if not section_enrollments:
            filter_note = f" matching '{student_status}'" if student_status in ("regular", "ex") else ""
            story.append(Paragraph(f"No enrollment numbers have data for this year yet{filter_note}.", styles["Normal"]))
            section_summaries.append((section["title"], 0, 0))
            continue
        if len(page_groups) > 1:
            story.append(Paragraph(
                f"Split across {len(page_groups)} page-groups below so every column stays "
                f"legible -- Sr.No./Enrollment No./Name/Program repeated on each.", styles["Normal"]))
        story.append(Spacer(1, 3))

        page_font_sizes = []
        for gi, group_blocks in enumerate(page_groups):
            cols_in_group = sum(b["n_cols"] for b in group_blocks)
            sub_col_w = avail_flex_w / cols_in_group
            sub_col_w = max(sub_col_w, MIN_COL_W) if sub_col_w < TARGET_COL_W else min(sub_col_w, TARGET_COL_W * 1.5)

            if sub_col_w >= 20:
                font_size = 7
            elif sub_col_w >= 16:
                font_size = 6
            elif sub_col_w >= 13:
                font_size = 5
            elif sub_col_w >= 9:
                font_size = 4.5
            else:
                font_size = 4
            page_font_sizes.append(font_size)
            leading = font_size + 1

            cell_style = styles["Normal"].clone(f"cell{si}_{gi}")
            cell_style.fontSize = font_size
            cell_style.leading = leading
            cell_style.alignment = TA_CENTER
            left_cell_style = cell_style.clone(f"cellleft{si}_{gi}")
            left_cell_style.alignment = TA_LEFT
            header_style = cell_style.clone(f"cellhdr{si}_{gi}")
            header_style.fontName = "Helvetica-Bold"
            header_style.alignment = TA_CENTER

            def P(text, style=cell_style):
                return Paragraph(str(clean_value(text)) if text not in (None, "") else "&nbsp;", style)

            col_widths = [srno_w * mm, enroll_w * mm, name_w * mm, program_w * mm] + [sub_col_w * mm] * cols_in_group

            header_rows = [[], []]
            header_rows[0] = [P("Sr.No.", header_style), P("Enrollment No", header_style),
                               P("Name of Student", header_style), P("Program", header_style)]
            header_rows[1] = [P("", header_style)] * 4
            for block in group_blocks:
                header_rows[0].append(P(block["label"], header_style))
                header_rows[0].extend([P("", header_style)] * (block["n_cols"] - 1))
                header_rows[1].extend(P(lbl, header_style) for lbl in block["sub_labels"])

            table_data = list(header_rows)
            for sr_no, enr in enumerate(section_enrollments, start=1):
                row = [P(sr_no), P(enr),
                       P(names_by_enr.get(enr, ""), left_cell_style),
                       P(programs_by_enr.get(enr, ""), left_cell_style)]
                for block in group_blocks:
                    row.extend(P(v) for v in block_row_values(block, enr))
                table_data.append(row)

            t = Table(table_data, colWidths=col_widths, repeatRows=2)
            style_cmds = [
                ("GRID", (0, 0), (-1, -1), 0.3, colors.grey),
                ("BACKGROUND", (0, 0), (-1, 1), colors.HexColor("#4472C4")),
                ("TEXTCOLOR", (0, 0), (-1, 1), colors.white),
                ("VALIGN", (0, 0), (-1, -1), "MIDDLE"),
                ("LEFTPADDING", (0, 0), (-1, -1), 1),
                ("RIGHTPADDING", (0, 0), (-1, -1), 1),
                ("TOPPADDING", (0, 0), (-1, -1), 1),
                ("BOTTOMPADDING", (0, 0), (-1, -1), 1),
                ("SPAN", (0, 0), (0, 1)),
                ("SPAN", (1, 0), (1, 1)),
                ("SPAN", (2, 0), (2, 1)),
                ("SPAN", (3, 0), (3, 1)),
            ]
            col_cursor = 4
            for block in group_blocks:
                col_from = col_cursor
                col_to = col_from + block["n_cols"] - 1
                style_cmds.append(("SPAN", (col_from, 0), (col_to, 0)))
                col_cursor += block["n_cols"]
            t.setStyle(TableStyle(style_cmds))

            if gi > 0:
                story.append(PageBreak())
                block_names = ", ".join(b["label"] for b in group_blocks)
                story.append(Paragraph(f"{section['title']} (continued -- {block_names})", styles["Normal"]))
                story.append(Spacer(1, 3))
            story.append(t)

        section_summaries.append((section["title"], len(section_enrollments), len(page_groups)))

    story.extend(build_report_end_flowables())
    doc.build(story)
    print(f"Saved PDF: {out_path}  (landscape A4, [{student_status}], {len(sections)} year section(s): " +
          ", ".join(f"{title} [{n_enr} enrollment(s), {n_pg} page-group(s)]"
                     for title, n_enr, n_pg in section_summaries) + ")")
    return out_path


def compute_yearly_eligibility_rows(db_path=DB_FILE, student_status="both"):
    """Build the row data for the Yearly Eligible/Non-Eligible Student
    List -- the SAME Eligible/Non-Eligible-for-Next-Year calculation
    generate_yearly_result_pdf()'s year block already makes, Rule 1 AND
    Rule 2 both included (see compute_year_eligibility_and_remark()),
    just pulled out as its own standalone Eligible/Not-Eligible listing
    per year instead of one column buried in the bigger Yearly Result
    report.

    Returns a list of (year_label, rows) tuples, one per active academic
    year (First Year / Second Year / Final Year -- whichever have data
    in the database), where each row is {enrollment, name, program,
    eligibility, remark}. remark is "Lower Semester Pending" whenever
    Rule 2 is what forced Not Eligible here (an unresolved failure still
    sitting in the immediately lower year), "" otherwise. An enrollment
    is left out of a year's list entirely if its eligibility isn't
    determinable yet (missing failed-count or subject-count data for
    that year), OR if this isn't that enrollment's HIGHEST year reached
    so far (an enrollment with Third/Fourth Semester data appears only
    in Second Year's list, never repeated in First Year's too). Within a
    year, rows are sorted Eligible first, then Not Eligible (enrollment
    number ascending within each group, same order build_student_history()
    already returns them in).
    """
    all_extracted, all_review = load_all_records_from_db(db_path)
    enrollments, programs_by_enr, names_by_enr, semesters, history = build_student_history(all_extracted, db_path)
    if not enrollments or not semesters:
        return []

    status_map = compute_student_status(all_extracted, db_path)

    subject_count_by_sem = compute_subject_count_by_semester(db_path)

    semesters_present = set(semesters)
    active_year_groups = [(prefix, sems) for prefix, sems in YEAR_GROUPS
                           if any(s in semesters_present for s in sems)]
    # Rule 2 needs "the immediately lower year" for a given year -- see
    # compute_year_eligibility_and_remark().
    year_position = {prefix: i for i, (prefix, _) in enumerate(active_year_groups)}

    def year_failed_count(enr, sems_in_year):
        recs = [history[(enr, s)] for s in sems_in_year if (enr, s) in history]
        if not recs:
            return ""
        return sum(r["failed_subjects"] for r in recs)

    def year_total_subjects(sems_in_year):
        present = [subject_count_by_sem[s] for s in sems_in_year if s in subject_count_by_sem]
        if not present:
            return ""
        return sum(present)

    def year_eligibility(enr, prefix, failed_count, total_subjects):
        idx = year_position.get(prefix)
        lower_failed = ""
        if idx is not None and idx > 0:
            _, lower_sems = active_year_groups[idx - 1]
            lower_failed = year_failed_count(enr, lower_sems)
        return compute_year_eligibility_and_remark(failed_count, total_subjects, lower_failed)

    def enrollments_touching(sems):
        wanted = {"regular": "Regular", "ex": "EX"}.get(student_status)
        touching = set()
        for enr, sem in history:
            if sem not in sems:
                continue
            if wanted is not None and status_map.get((enr, sem)) != wanted:
                continue
            touching.add(enr)
        return [enr for enr in enrollments if enr in touching]

    # An enrollment that's reached a higher year is listed ONLY under
    # that highest year -- not repeated under every lower year it's
    # since moved past. Same rule as generate_yearly_result_pdf().
    def highest_year_index(enr):
        highest = None
        for i, (_, sems) in enumerate(active_year_groups):
            if any((enr, s) in history for s in sems):
                highest = i
        return highest

    highest_year_by_enr = {enr: highest_year_index(enr) for enr in enrollments}

    results = []
    for year_idx, (prefix, sems_in_year) in enumerate(active_year_groups):
        sems_in_data = [s for s in sems_in_year if s in semesters_present]
        total_subj = year_total_subjects(sems_in_year)

        rows = []
        for enr in enrollments_touching(sems_in_data):
            if highest_year_by_enr.get(enr) != year_idx:
                continue  # this enrollment has since moved past this year
            failed = year_failed_count(enr, sems_in_year)
            eligibility, remark = year_eligibility(enr, prefix, failed, total_subj)
            if eligibility == "":
                continue  # not determinable yet -- this list only shows a definite call
            rows.append({
                "enrollment": enr,
                "name": names_by_enr.get(enr, ""),
                "program": programs_by_enr.get(enr, ""),
                "eligibility": eligibility,
                "remark": remark,
            })

        # Eligible enrollments first, then Not Eligible -- stable sort
        # keeps ascending enrollment-number order within each group,
        # since `enrollments` (and so `rows`) already came in that order.
        rows.sort(key=lambda r: 0 if r["eligibility"] == "Eligible" else 1)
        results.append((prefix, rows))

    return results


def generate_yearly_eligibility_pdf(db_path=DB_FILE, out_path=None, student_status="both"):
    """Build the Yearly Eligible/Non-Eligible Student List as one
    print-ready landscape A4 PDF: the report heading block first
    ("Yearly_Eligible_NonEligible_Report" / Institute Name+Address /
    Program / Academic Year -- see build_yearly_eligibility_heading_flowables()
    -- using whichever semester is the LATEST one found in the database,
    since this report spans every year at once), then one section per
    academic year (each starting on its own fresh page, a year with no
    determinable rows skipped entirely) -- see compute_yearly_eligibility_rows()
    for the Eligible/Not-Eligible rule and sort order -- then the
    signature block once at the very end (see build_report_end_flowables()).

    Columns: Sr. No. / Enrollment No / Name of Student / Program /
    Eligible/Non-Eligible / Remark ("Lower Semester Pending" when Rule 2
    is what forced Not Eligible here, "" otherwise).
    """
    from reportlab.lib.pagesizes import A4, landscape
    from reportlab.platypus import SimpleDocTemplate, Table, TableStyle, Paragraph, Spacer, PageBreak
    from reportlab.lib.styles import getSampleStyleSheet
    from reportlab.lib.enums import TA_CENTER, TA_LEFT
    from reportlab.lib import colors
    from reportlab.lib.units import mm

    styles = getSampleStyleSheet()
    font_size = 9
    cell_style = styles["Normal"].clone("eligcell")
    cell_style.fontSize = font_size
    cell_style.leading = font_size + 2
    cell_style.alignment = TA_CENTER
    left_cell_style = cell_style.clone("eligcellleft")
    left_cell_style.alignment = TA_LEFT
    header_style = cell_style.clone("eligchdr")
    header_style.fontName = "Helvetica-Bold"
    header_style.alignment = TA_CENTER

    def P(text, style=cell_style):
        return Paragraph(str(text) if text not in (None, "") else "&nbsp;", style)

    COLUMNS = [
        ("Sr. No.", 10), ("Enrollment No", 22), ("Name of Student", 40),
        ("Program", 38), ("Eligible/Non-Eligible", 20), ("Remark", 22),
    ]
    ELIG_COL = 4
    page_w_mm, margin_mm = 297, 4
    usable_w_mm = page_w_mm - 2 * margin_mm
    raw_widths = [w for _, w in COLUMNS]
    scale = usable_w_mm / sum(raw_widths)
    col_widths = [w * scale * mm for w in raw_widths]

    out_path = out_path or "Yearly_Eligible_NonEligible_Report.pdf"
    doc = SimpleDocTemplate(out_path, pagesize=landscape(A4),
                             leftMargin=margin_mm * mm, rightMargin=margin_mm * mm,
                             topMargin=margin_mm * mm, bottomMargin=margin_mm * mm)

    # Program/Academic Year in the heading represent the LATEST semester
    # found in the database -- this report spans every year at once, so
    # there's no single "this semester" to anchor those fields to.
    all_extracted, _ = load_all_records_from_db(db_path)
    semesters_in_db = sorted({r["semester_label"] for r in all_extracted if r["enrollment"]},
                              key=lambda s: SEMESTER_NAMES.index(s) if s in SEMESTER_NAMES else 999)
    latest_semester = semesters_in_db[-1] if semesters_in_db else None
    story = build_yearly_eligibility_heading_flowables(latest_semester, db_path)
    included_years = []

    year_data = compute_yearly_eligibility_rows(db_path, student_status)
    if not year_data:
        print(f"No student data found for the Yearly Eligible/Non-Eligible list [{student_status}] in {db_path}.")
        return None

    for year_label, rows in year_data:
        if not rows:
            print(f"  Skipping {year_label} -- no enrollment with a determinable eligibility yet.")
            continue

        if included_years:
            story.append(PageBreak())  # every year starts on its own fresh page
        included_years.append(year_label)

        status_note = {"regular": " (Regular)", "ex": " (EX)", "both": ""}.get(student_status, "")
        story.append(Paragraph(f"{year_label} -- Eligible/Non-Eligible Student List{status_note}",
                                styles["Heading2"]))
        story.append(Spacer(1, 3))
        year_semesters = dict(YEAR_GROUPS).get(year_label, [])
        gap_style = styles["Normal"].clone(f"eliggap{year_label}")
        gap_style.fontSize = 8
        gap_warn_style = gap_style.clone(f"eliggapwarn{year_label}")
        gap_warn_style.textColor = colors.HexColor("#B30000")
        if year_semesters:
            for i, line in enumerate(_report_seating_gap_lines(year_semesters, student_status, db_path)):
                story.append(Paragraph(line, gap_warn_style if i > 0 else gap_style))
        story.append(Spacer(1, 3))

        header = [P(label, header_style) for label, _ in COLUMNS]
        table_data = [header]
        style_cmds = [
            ("GRID", (0, 0), (-1, -1), 0.3, colors.grey),
            ("BACKGROUND", (0, 0), (-1, 0), colors.HexColor("#4472C4")),
            ("TEXTCOLOR", (0, 0), (-1, 0), colors.white),
            ("VALIGN", (0, 0), (-1, -1), "MIDDLE"),
            ("LEFTPADDING", (0, 0), (-1, -1), 3),
            ("RIGHTPADDING", (0, 0), (-1, -1), 3),
            ("TOPPADDING", (0, 0), (-1, -1), 2),
            ("BOTTOMPADDING", (0, 0), (-1, -1), 2),
        ]
        for sr_no, row in enumerate(rows, start=1):
            table_data.append([
                P(sr_no),
                P(row["enrollment"]),
                P(row["name"], left_cell_style),
                P(row["program"], left_cell_style),
                P(row["eligibility"]),
                P(row["remark"], left_cell_style),
            ])
            if row["eligibility"] == "Not Eligible":
                style_cmds.append(("BACKGROUND", (ELIG_COL, sr_no), (ELIG_COL, sr_no),
                                    colors.HexColor("#FFA500")))

        t = Table(table_data, colWidths=col_widths, repeatRows=1)
        t.setStyle(TableStyle(style_cmds))
        story.append(t)
        story.append(Spacer(1, 10))

    if not included_years:
        print(f"No enrollments with a determinable eligibility yet [{student_status}] in {db_path}.")
        return None

    story.extend(build_report_end_flowables())
    doc.build(story)
    print(f"Saved PDF: {out_path}  (landscape A4, Yearly Eligible/Non-Eligible List, [{student_status}], "
          f"{len(included_years)} year section(s))")
    return out_path


def compute_topper_lists(db_path=DB_FILE, student_status="both", top_n=5):
    """Build the Top-N rankers for the "Semesterwise and Yearly Topper
    List" report:
      - Semester toppers: for each semester, the top N enrollments by
        THAT SEMESTER's own Percentage -- every appeared enrollment is a
        candidate, no eligibility filter (eligibility isn't defined at
        the semester level, only at the year level).
      - Year toppers: for each academic year, the top N enrollments by
        THAT YEAR's average Percentage (mean of the year's semester(s)
        Percentage) -- ELIGIBLE enrollments ONLY, using the exact same
        Eligible/Non-Eligible call (Rule 1 + Rule 2, "shown only under
        the enrollment's highest year reached") as
        compute_yearly_eligibility_rows(), so the topper list can never
        include someone that report doesn't also call Eligible.

    Both lists respect student_status the same way every other report
    does (filters which enrollments are candidates at all).

    Returns (semester_toppers, year_toppers):
      semester_toppers: [(semester_label, academic_year, [row, ...]), ...]
      year_toppers:      [(year_label, academic_year, [row, ...]), ...]
    where each row is {rank, enrollment, name, program, percentage}.
    A semester/year with no enrollment having a usable Percentage yet
    still appears in the list, just with an empty row list, so the
    caller can print a "skipped" note rather than silently vanishing it.
    """
    all_extracted, _ = load_all_records_from_db(db_path)
    enrollments, programs_by_enr, names_by_enr, semesters, history = build_student_history(all_extracted, db_path)
    if not enrollments or not semesters:
        return [], []

    status_map = compute_student_status(all_extracted, db_path)
    wanted = {"regular": "Regular", "ex": "EX"}.get(student_status)

    def parse_pct(value):
        # Tolerates a trailing '%' (e.g. someone typed/pasted "31%"
        # rather than "31" during Offline Import) -- without this, a
        # percent sign silently fails float() and drops that student out
        # of every ranked list with no error, which is exactly what
        # happened before this fix.
        if value in (None, ""):
            return None
        try:
            return float(str(value).strip().rstrip("%").strip())
        except ValueError:
            return None

    semesters_present = set(semesters)
    semesters_sorted = sorted(semesters_present,
                               key=lambda s: SEMESTER_NAMES.index(s) if s in SEMESTER_NAMES else 999)

    def rank_rows(candidates):
        # candidates: [(percentage, enrollment), ...] -- highest first,
        # enrollment number as a stable tie-break for ordering only (not
        # for the rank NUMBER itself). This uses DENSE ranking: equal
        # scores share a rank, and the NEXT distinct (lower) score always
        # steps up by exactly 1 from whatever rank came before it -- e.g.
        # three students tied at rank 4 are followed by rank 5 (not rank
        # 7), and if MULTIPLE students share that 5th rank too, all of
        # them are included, not just one. "Top N" means N distinct
        # ranking positions get shown, however many rows that takes once
        # ties are accounted for -- the cutoff below stops as soon as a
        # NEW rank would exceed top_n, but never mid-way through a tied
        # group that's still AT top_n.
        candidates.sort(key=lambda t: (-t[0], t[1]))
        rows = []
        prev_pct = None
        rank = 0
        for pct, enr in candidates:
            if prev_pct is None or pct != prev_pct:
                rank += 1
                if rank > top_n:
                    break
            rows.append({"rank": rank, "enrollment": enr, "name": names_by_enr.get(enr, ""),
                         "program": programs_by_enr.get(enr, ""), "percentage": pct})
            prev_pct = pct
        return rows

    # --- Semester toppers ---
    semester_toppers = []
    for sem in semesters_sorted:
        candidates = []
        for enr in enrollments:
            if wanted is not None and status_map.get((enr, sem)) != wanted:
                continue
            rec = history.get((enr, sem))
            if not rec:
                continue
            pct = parse_pct(rec["percentage"])
            if pct is not None:
                candidates.append((pct, enr))
        _, _, academic_year, _ = parse_exam_session(get_semester_identity_text(sem, "year", db_path))
        semester_toppers.append((sem, academic_year, rank_rows(candidates)))

    # --- Year toppers (eligible only) ---
    active_year_groups = [(prefix, sems) for prefix, sems in YEAR_GROUPS
                           if any(s in semesters_present for s in sems)]
    sems_by_year = dict(active_year_groups)
    eligibility_by_year = compute_yearly_eligibility_rows(db_path, student_status)

    def year_average_pct(enr, sems_in_year):
        values = [parse_pct(history[(enr, s)]["percentage"]) for s in sems_in_year if (enr, s) in history]
        values = [v for v in values if v is not None]
        return round(sum(values) / len(values), 2) if values else None

    year_toppers = []
    for prefix, elig_rows in eligibility_by_year:
        sems_in_year = sems_by_year.get(prefix, [])
        candidates = []
        for r in elig_rows:
            if r["eligibility"] != "Eligible":
                continue
            avg = year_average_pct(r["enrollment"], sems_in_year)
            if avg is not None:
                candidates.append((avg, r["enrollment"]))
        sems_with_data = [s for s in sems_in_year if s in semesters_present]
        rep_sem = sems_with_data[-1] if sems_with_data else None
        academic_year = ""
        if rep_sem:
            _, _, academic_year, _ = parse_exam_session(get_semester_identity_text(rep_sem, "year", db_path))
        year_toppers.append((prefix, academic_year, rank_rows(candidates)))

    return semester_toppers, year_toppers


def generate_topper_list_pdf(db_path=DB_FILE, out_path=None, student_status="both", top_n=5):
    """Build the "Semesterwise and Yearly Topper List" report as one
    print-ready landscape A4 PDF: the report heading first (see
    build_topper_list_heading_flowables(), using the latest semester in
    the database for Program/Academic Year), then one small Top-N table
    per semester (by that semester's own Percentage) and one small Top-N
    table per academic year (by that year's average Percentage, ELIGIBLE
    enrollments only -- see compute_topper_lists()), then the common
    signature block once at the very end (see build_report_end_flowables()).

    Columns: Year | Program | Semester (or Year, depending on the table)
    | Rank | Enrollment No | Student Name | Semester Percentage (or
    Yearly Percentage).
    """
    from reportlab.lib.pagesizes import A4, landscape
    from reportlab.platypus import SimpleDocTemplate, Table, TableStyle, Paragraph, Spacer
    from reportlab.lib.styles import getSampleStyleSheet
    from reportlab.lib.enums import TA_CENTER, TA_LEFT
    from reportlab.lib import colors
    from reportlab.lib.units import mm

    styles = getSampleStyleSheet()
    font_size = 9
    cell_style = styles["Normal"].clone("topcell")
    cell_style.fontSize = font_size
    cell_style.leading = font_size + 2
    cell_style.alignment = TA_CENTER
    left_cell_style = cell_style.clone("topcellleft")
    left_cell_style.alignment = TA_LEFT
    header_style = cell_style.clone("tophdr")
    header_style.fontName = "Helvetica-Bold"
    header_style.alignment = TA_CENTER

    def P(text, style=cell_style):
        return Paragraph(str(text) if text not in (None, "") else "&nbsp;", style)

    def make_columns(period_label, pct_label):
        return [
            ("Year", 14), ("Program", 42), (period_label, 18), ("Rank", 9),
            ("Enrollment No", 22), ("Student Name", 36), (pct_label, 18),
        ]

    page_w_mm, margin_mm = 297, 4
    usable_w_mm = page_w_mm - 2 * margin_mm

    def col_widths_for(columns):
        raw_widths = [w for _, w in columns]
        scale = usable_w_mm / sum(raw_widths)
        return [w * scale * mm for w in raw_widths]

    def render_table(story, title, columns, period_value, academic_year, rows):
        story.append(Paragraph(title, styles["Heading3"]))
        story.append(Spacer(1, 3))
        if not rows:
            story.append(Paragraph("No eligible/ranked enrollments found for this list yet.", styles["Normal"]))
            story.append(Spacer(1, 10))
            return
        header = [P(label, header_style) for label, _ in columns]
        table_data = [header]
        for row in rows:
            table_data.append([
                P(academic_year),
                P(row["program"], left_cell_style),
                P(period_value),
                P(row["rank"]),
                P(row["enrollment"]),
                P(row["name"], left_cell_style),
                P(f"{row['percentage']:.2f}"),
            ])
        t = Table(table_data, colWidths=col_widths_for(columns))
        t.setStyle(TableStyle([
            ("GRID", (0, 0), (-1, -1), 0.3, colors.grey),
            ("BACKGROUND", (0, 0), (-1, 0), colors.HexColor("#4472C4")),
            ("TEXTCOLOR", (0, 0), (-1, 0), colors.white),
            ("VALIGN", (0, 0), (-1, -1), "MIDDLE"),
            ("LEFTPADDING", (0, 0), (-1, -1), 3),
            ("RIGHTPADDING", (0, 0), (-1, -1), 3),
            ("TOPPADDING", (0, 0), (-1, -1), 2),
            ("BOTTOMPADDING", (0, 0), (-1, -1), 2),
        ]))
        story.append(t)
        story.append(Spacer(1, 10))

    semester_toppers, year_toppers = compute_topper_lists(db_path, student_status, top_n)
    if not semester_toppers and not year_toppers:
        print(f"No student data found for the Topper List [{student_status}] in {db_path}.")
        return None

    all_extracted, _ = load_all_records_from_db(db_path)
    semesters_in_db = sorted({r["semester_label"] for r in all_extracted if r["enrollment"]},
                              key=lambda s: SEMESTER_NAMES.index(s) if s in SEMESTER_NAMES else 999)
    latest_semester = semesters_in_db[-1] if semesters_in_db else None

    out_path = out_path or "Semesterwise_and_Yearly_Topper_List.pdf"
    doc = SimpleDocTemplate(out_path, pagesize=landscape(A4),
                             leftMargin=margin_mm * mm, rightMargin=margin_mm * mm,
                             topMargin=margin_mm * mm, bottomMargin=margin_mm * mm)
    story = build_topper_list_heading_flowables(latest_semester, db_path)

    status_note = {"regular": " (Regular)", "ex": " (EX)", "both": ""}.get(student_status, "")
    sem_columns = make_columns("Semester", "Semester Percentage")
    year_columns = make_columns("Year", "Yearly Percentage")

    for sem_label, academic_year, rows in semester_toppers:
        render_table(story, f"Top {top_n} -- {sem_label.title()}{status_note}",
                     sem_columns, sem_label.title(), academic_year, rows)

    for year_label, academic_year, rows in year_toppers:
        render_table(story, f"Top {top_n} -- {year_label} (Eligible Students){status_note}",
                     year_columns, year_label, academic_year, rows)

    story.extend(build_report_end_flowables())
    doc.build(story)
    print(f"Saved PDF: {out_path}  (landscape A4, Semesterwise and Yearly Topper List, [{student_status}], "
          f"{len(semester_toppers)} semester list(s), {len(year_toppers)} year list(s))")
    return out_path


def compute_bright_weak_lists(db_path=DB_FILE, student_status="both",
                               weak_threshold=40.0, bright_threshold=75.0):
    """Build the per-semester Weak/Bright student lists for the "Semester
    wise Bright/Weak Student List" report.

    For each semester found in the database, every appeared enrollment
    (respecting student_status the same way every other report does) is
    classified purely on THAT semester's own Percentage:
      - Percentage < weak_threshold      -> Weak list (sorted weakest
        first, i.e. lowest percentage first).
      - Percentage > bright_threshold    -> Bright list (sorted
        strongest first, i.e. highest percentage first).
      - Anything in between (weak_threshold <= pct <= bright_threshold)
        is neither weak nor bright and is left out of both lists.
    A student with no usable Percentage for a semester is skipped for
    that semester entirely (not counted as weak or bright).

    Returns a list of tuples, one per semester (in semester order):
        (semester_label, academic_year, year_label, weak_rows, bright_rows)
    where year_label is the "First Year"/"Second Year"/"Final Year"
    academic-year group that semester belongs to (from YEAR_GROUPS), and
    each row in weak_rows/bright_rows is
        {"enrollment", "name", "program", "percentage"}.
    A semester with no enrollments at all yet still appears (with empty
    weak_rows/bright_rows) so the caller can note it was skipped rather
    than silently vanishing it.
    """
    all_extracted, _ = load_all_records_from_db(db_path)
    enrollments, programs_by_enr, names_by_enr, semesters, history = build_student_history(all_extracted, db_path)
    if not enrollments or not semesters:
        return []

    status_map = compute_student_status(all_extracted, db_path)
    wanted = {"regular": "Regular", "ex": "EX"}.get(student_status)

    def parse_pct(value):
        # Tolerates a trailing '%' (e.g. someone typed/pasted "31%"
        # rather than "31" during Offline Import) -- without this, a
        # percent sign silently fails float() and drops that student out
        # of every ranked list with no error, which is exactly what
        # happened before this fix.
        if value in (None, ""):
            return None
        try:
            return float(str(value).strip().rstrip("%").strip())
        except ValueError:
            return None

    def year_label_for(sem):
        for prefix, sems in YEAR_GROUPS:
            if sem in sems:
                return prefix
        return ""

    semesters_present = set(semesters)
    semesters_sorted = sorted(semesters_present,
                               key=lambda s: SEMESTER_NAMES.index(s) if s in SEMESTER_NAMES else 999)

    results = []
    for sem in semesters_sorted:
        weak_rows, bright_rows = [], []
        for enr in enrollments:
            if wanted is not None and status_map.get((enr, sem)) != wanted:
                continue
            rec = history.get((enr, sem))
            if not rec:
                continue
            pct = parse_pct(rec["percentage"])
            if pct is None:
                continue
            entry = {"enrollment": enr, "name": names_by_enr.get(enr, ""),
                      "program": programs_by_enr.get(enr, ""), "percentage": pct}
            if pct < weak_threshold:
                weak_rows.append(entry)
            elif pct > bright_threshold:
                bright_rows.append(entry)
        weak_rows.sort(key=lambda r: (r["percentage"], r["enrollment"]))      # weakest first
        bright_rows.sort(key=lambda r: (-r["percentage"], r["enrollment"]))   # strongest first
        _, _, academic_year, _ = parse_exam_session(get_semester_identity_text(sem, "year", db_path))
        results.append((sem, academic_year, year_label_for(sem), weak_rows, bright_rows))

    return results


def generate_bright_weak_pdf(db_path=DB_FILE, out_path=None, student_status="both",
                              weak_threshold=40.0, bright_threshold=75.0):
    """Build the "Semester wise Bright/Weak Student List" as one print-
    ready landscape A4 PDF: the common report heading first (see
    build_bright_weak_heading_flowables(), using the latest semester in
    the database for Program/Academic Year), then one table per semester
    -- Weak Students (Percentage below weak_threshold) listed first,
    Bright Students (Percentage above bright_threshold) listed below in
    the SAME table -- see compute_bright_weak_lists() -- and finally the
    common signature block once at the very end (see
    build_report_end_flowables()).

    Columns: Year | Program | Sr. No. | Enrollment Number | Student Name
    | Percentage. Sr. No. restarts at 1 for the Weak group and again at
    1 for the Bright group within each semester's table.
    """
    from reportlab.lib.pagesizes import A4, landscape
    from reportlab.platypus import SimpleDocTemplate, Table, TableStyle, Paragraph, Spacer, PageBreak
    from reportlab.lib.styles import getSampleStyleSheet
    from reportlab.lib.enums import TA_CENTER, TA_LEFT
    from reportlab.lib import colors
    from reportlab.lib.units import mm

    styles = getSampleStyleSheet()
    font_size = 9
    cell_style = styles["Normal"].clone("bwcell")
    cell_style.fontSize = font_size
    cell_style.leading = font_size + 2
    cell_style.alignment = TA_CENTER
    left_cell_style = cell_style.clone("bwcellleft")
    left_cell_style.alignment = TA_LEFT
    header_style = cell_style.clone("bwhdr")
    header_style.fontName = "Helvetica-Bold"
    header_style.alignment = TA_CENTER
    section_style = cell_style.clone("bwsection")
    section_style.fontName = "Helvetica-Bold"
    section_style.alignment = TA_LEFT
    section_style.fontSize = font_size + 1

    def P(text, style=cell_style):
        return Paragraph(str(text) if text not in (None, "") else "&nbsp;", style)

    COLUMNS = [
        ("Year", 16), ("Program", 42), ("Sr. No.", 10),
        ("Enrollment Number", 24), ("Student Name", 42), ("Percentage", 16),
    ]
    N_COLS = len(COLUMNS)
    page_w_mm, margin_mm = 297, 4
    usable_w_mm = page_w_mm - 2 * margin_mm
    raw_widths = [w for _, w in COLUMNS]
    scale = usable_w_mm / sum(raw_widths)
    col_widths = [w * scale * mm for w in raw_widths]

    def render_section(table_data, style_cmds, title, bg_color, rows, year_label, program, academic_year):
        row_idx = len(table_data)
        table_data.append([P(title, section_style)] + [P("")] * (N_COLS - 1))
        style_cmds.append(("SPAN", (0, row_idx), (N_COLS - 1, row_idx)))
        style_cmds.append(("BACKGROUND", (0, row_idx), (N_COLS - 1, row_idx), bg_color))

        header_idx = row_idx + 1
        table_data.append([P(label, header_style) for label, _ in COLUMNS])
        style_cmds.append(("BACKGROUND", (0, header_idx), (-1, header_idx), colors.HexColor("#4472C4")))
        style_cmds.append(("TEXTCOLOR", (0, header_idx), (-1, header_idx), colors.white))

        if not rows:
            note_idx = header_idx + 1
            table_data.append([P("No students found in this list.", left_cell_style)] + [P("")] * (N_COLS - 1))
            style_cmds.append(("SPAN", (0, note_idx), (N_COLS - 1, note_idx)))
            return
        for sr_no, row in enumerate(rows, start=1):
            table_data.append([
                P(year_label),
                P(program, left_cell_style),
                P(sr_no),
                P(row["enrollment"]),
                P(row["name"], left_cell_style),
                P(f"{row['percentage']:.2f}"),
            ])

    out_path = out_path or "Semesterwise_Bright_Weak_Student_List.pdf"
    doc = SimpleDocTemplate(out_path, pagesize=landscape(A4),
                             leftMargin=margin_mm * mm, rightMargin=margin_mm * mm,
                             topMargin=margin_mm * mm, bottomMargin=margin_mm * mm)

    all_extracted, _ = load_all_records_from_db(db_path)
    semesters_in_db = sorted({r["semester_label"] for r in all_extracted if r["enrollment"]},
                              key=lambda s: SEMESTER_NAMES.index(s) if s in SEMESTER_NAMES else 999)
    latest_semester = semesters_in_db[-1] if semesters_in_db else None
    story = build_bright_weak_heading_flowables(latest_semester, db_path)

    semester_data = compute_bright_weak_lists(db_path, student_status, weak_threshold, bright_threshold)
    if not semester_data:
        print(f"No student data found for the Bright/Weak Student List [{student_status}] in {db_path}.")
        return None

    status_note = {"regular": " (Regular)", "ex": " (EX)", "both": ""}.get(student_status, "")
    included_semesters = []
    for sem_label, academic_year, year_label, weak_rows, bright_rows in semester_data:
        if not weak_rows and not bright_rows:
            print(f"  Skipping {sem_label} -- no weak or bright students found for this semester yet.")
            continue

        if included_semesters:
            story.append(PageBreak())  # every semester starts on its own fresh page
        included_semesters.append(sem_label)

        program = get_semester_identity_text(sem_label, "program", db_path)
        story.append(Paragraph(f"{sem_label.title()}{status_note}", styles["Heading2"]))
        story.append(Spacer(1, 3))

        table_data = []
        style_cmds = [
            ("GRID", (0, 0), (-1, -1), 0.3, colors.grey),
            ("VALIGN", (0, 0), (-1, -1), "MIDDLE"),
            ("LEFTPADDING", (0, 0), (-1, -1), 3),
            ("RIGHTPADDING", (0, 0), (-1, -1), 3),
            ("TOPPADDING", (0, 0), (-1, -1), 2),
            ("BOTTOMPADDING", (0, 0), (-1, -1), 2),
        ]
        render_section(table_data, style_cmds, f"Weak Students (Percentage below {weak_threshold:g}%)",
                       colors.HexColor("#F8CBAD"), weak_rows, year_label, program, academic_year)
        render_section(table_data, style_cmds, f"Bright Students (Percentage above {bright_threshold:g}%)",
                       colors.HexColor("#C6E0B4"), bright_rows, year_label, program, academic_year)

        t = Table(table_data, colWidths=col_widths)
        t.setStyle(TableStyle(style_cmds))
        story.append(t)
        story.append(Spacer(1, 10))

    if not included_semesters:
        print(f"No weak or bright students found yet [{student_status}] in {db_path}.")
        return None

    story.extend(build_report_end_flowables())
    doc.build(story)
    print(f"Saved PDF: {out_path}  (landscape A4, Semester wise Bright/Weak Student List, [{student_status}], "
          f"weak<{weak_threshold:g}%, bright>{bright_threshold:g}%, {len(included_semesters)} semester(s))")
    return out_path


def ask_report_selection():
    """Checkbox dialog: which report(s) to build (Semester-wise, History
    of Student, K7 (Part B), K7 (Part C)), and for each one ticked,
    whether to include Regular students only, EX students only, or both
    -- per compute_student_status(). The K7 (Part B) block also has a
    "Highlight Failed % above" entry box -- any row whose Failed %
    exceeds that number gets an orange highlight in the PDF.

    The report list scrolls (mouse wheel or the scrollbar) inside a fixed-
    size window, with the "Generate" button always pinned below it --
    so the dialog stays usable as more report types get added, instead
    of growing until it runs off the bottom of a shorter screen.

    K7 (Part B) additionally requires Abbreviation/Course Code to have
    been entered at least once (see course_codes_are_filled()) -- its
    block has a "Enter Course Codes..." button that opens
    run_course_code_entry_dialog() directly, with a tick/warning label
    next to it reflecting current DB state (checked fresh on dialog open,
    and again right after that button closes). If K7 (Part B) is ticked
    but course codes still aren't filled in when Generate is pressed,
    a warning dialog blocks submission until either the codes are
    entered or the K7 (Part B) checkbox is unticked.

    Returns {"semester": None|"regular"|"ex"|"both",
             "yearly_result": None|"regular"|"ex"|"both",
             "k7_partb": None|"regular"|"ex"|"both",
             "k7b_fail_threshold": float,
             "k7_partc": None|"regular"|"ex"|"both",
             "yearly_eligibility": None|"regular"|"ex"|"both",
             "topper_list": None|"regular"|"ex"|"both",
             "bright_weak": None|"regular"|"ex"|"both",
             "bw_weak_threshold": float,
             "bw_bright_threshold": float}
    -- None for a report means its checkbox was left unticked (skip it
    entirely). Defaults to every report ticked, "both" status, 30%
    highlight threshold, weak below 40% / bright above 75%, if the
    dialog is closed without changes.
    """
    root = tk.Toplevel(_get_app_root())
    root.title("Which report(s) to build?")
    root.resizable(False, False)
    root.attributes("-topmost", True)
    root.geometry("560x560")

    result = {"semester": "both", "yearly_result": "both", "k7_partb": "both", "k7b_fail_threshold": 30.0,
              "k7_partc": "both", "yearly_eligibility": "both", "topper_list": "both",
              "bright_weak": "both", "bw_weak_threshold": 40.0, "bw_bright_threshold": 75.0}

    tk.Label(root, text="Select which report(s) to generate:", font=("Arial", 11, "bold")).pack(
        anchor="w", padx=12, pady=(12, 8))

    # Everything below scrolls (mouse wheel or the scrollbar) -- the
    # report list keeps growing as new report types get added, and this
    # keeps the dialog usable on a short screen instead of running off
    # the bottom with no way to reach "Generate".
    main_frame = tk.Frame(root)
    main_frame.pack(fill="both", expand=True)
    canvas = tk.Canvas(main_frame, highlightthickness=0)
    scrollbar = ttk.Scrollbar(main_frame, orient="vertical", command=canvas.yview)
    scroll_frame = tk.Frame(canvas)
    scroll_frame.bind("<Configure>", lambda e: canvas.configure(scrollregion=canvas.bbox("all")))
    canvas_window = canvas.create_window((0, 0), window=scroll_frame, anchor="nw")
    canvas.configure(yscrollcommand=scrollbar.set)
    canvas.bind("<Configure>", lambda e: canvas.itemconfig(canvas_window, width=e.width))
    canvas.pack(side="left", fill="both", expand=True, padx=(12, 0), pady=5)
    scrollbar.pack(side="left", fill="y")

    def _on_mousewheel(event):
        canvas.yview_scroll(int(-1 * (event.delta / 120)), "units")
    canvas.bind("<Enter>", lambda e: canvas.bind_all("<MouseWheel>", _on_mousewheel))
    canvas.bind("<Leave>", lambda e: canvas.unbind_all("<MouseWheel>"))

    sem_var = tk.IntVar(value=1)
    yr_var = tk.IntVar(value=1)
    k7b_var = tk.IntVar(value=1)
    k7c_var = tk.IntVar(value=1)
    elig_var = tk.IntVar(value=1)
    topper_var = tk.IntVar(value=1)
    bw_var = tk.IntVar(value=1)
    sem_status_var = tk.StringVar(value="both")
    yr_status_var = tk.StringVar(value="both")
    k7b_status_var = tk.StringVar(value="both")
    k7b_threshold_var = tk.StringVar(value="30")
    k7c_status_var = tk.StringVar(value="both")
    elig_status_var = tk.StringVar(value="both")
    topper_status_var = tk.StringVar(value="both")
    bw_status_var = tk.StringVar(value="both")
    bw_weak_threshold_var = tk.StringVar(value="40")
    bw_bright_threshold_var = tk.StringVar(value="75")

    STATUS_OPTIONS = [("Regular students only", "regular"), ("EX students only", "ex"),
                       ("Both Regular and EX", "both")]

    def make_report_block(label_text, check_var, status_var, extra=None):
        frame = tk.Frame(scroll_frame)
        frame.pack(anchor="w", padx=12, pady=6, fill="x")
        tk.Checkbutton(frame, text=label_text, variable=check_var,
                       font=("Arial", 10, "bold")).pack(anchor="w")
        sub = tk.Frame(frame)
        sub.pack(anchor="w", padx=26)
        for label, value in STATUS_OPTIONS:
            tk.Radiobutton(sub, text=label, variable=status_var, value=value).pack(anchor="w")
        if extra:
            extra(sub)

    course_code_status_label = {"widget": None}

    def refresh_course_code_status():
        lbl = course_code_status_label["widget"]
        if lbl is None:
            return
        if course_codes_are_filled(DB_FILE):
            lbl.config(text="\u2713 Course codes entered", fg="#1a7a1a")
        else:
            lbl.config(text="\u26a0 Course codes NOT entered yet -- required for K7 (Part B)", fg="#b30000")

    def open_course_code_dialog():
        run_course_code_entry_dialog(DB_FILE)
        refresh_course_code_status()

    def k7b_extra(sub):
        row = tk.Frame(sub)
        row.pack(anchor="w", pady=(6, 0))
        tk.Label(row, text="Highlight Failed % above:").pack(side="left")
        tk.Entry(row, textvariable=k7b_threshold_var, width=6).pack(side="left", padx=4)
        tk.Label(row, text="%").pack(side="left")

        cc_row = tk.Frame(sub)
        cc_row.pack(anchor="w", pady=(8, 0), fill="x")
        ttk.Button(cc_row, text="Enter Course Codes...", command=open_course_code_dialog).pack(side="left")
        status_lbl = tk.Label(cc_row, text="", font=("Arial", 9))
        status_lbl.pack(side="left", padx=8)
        course_code_status_label["widget"] = status_lbl

    def bw_extra(sub):
        row = tk.Frame(sub)
        row.pack(anchor="w", pady=(6, 0))
        tk.Label(row, text="Weak: Percentage below").pack(side="left")
        tk.Entry(row, textvariable=bw_weak_threshold_var, width=6).pack(side="left", padx=4)
        tk.Label(row, text="%").pack(side="left")

        row2 = tk.Frame(sub)
        row2.pack(anchor="w", pady=(4, 0))
        tk.Label(row2, text="Bright: Percentage above").pack(side="left")
        tk.Entry(row2, textvariable=bw_bright_threshold_var, width=6).pack(side="left", padx=4)
        tk.Label(row2, text="%").pack(side="left")

    make_report_block("Semester-wise Report(s)", sem_var, sem_status_var)
    make_report_block("Yearly Result Report", yr_var, yr_status_var)
    make_report_block("K7 (Part B) Report", k7b_var, k7b_status_var, extra=k7b_extra)
    make_report_block("K7 (Part C) Report", k7c_var, k7c_status_var)
    make_report_block("Yearly Eligible/Non-Eligible Student List", elig_var, elig_status_var)
    make_report_block("Semesterwise and Yearly Topper List", topper_var, topper_status_var)
    make_report_block("Semester wise Bright/Weak Student List", bw_var, bw_status_var, extra=bw_extra)

    refresh_course_code_status()  # reflect DB state as it already is, before any button click

    def submit():
        if k7b_var.get() and not course_codes_are_filled(DB_FILE):
            messagebox.showwarning(
                "Course codes required",
                "K7 (Part B) is ticked, but no Abbreviation/Course Code has been entered yet.\n\n"
                "Click \"Enter Course Codes...\" and save at least one subject's Abbreviation and "
                "Course Code, or untick K7 (Part B) Report to continue without it.")
            return  # keep the dialog open -- this is a hard requirement, not a soft warning
        result["semester"] = sem_status_var.get() if sem_var.get() else None
        result["yearly_result"] = yr_status_var.get() if yr_var.get() else None
        result["k7_partb"] = k7b_status_var.get() if k7b_var.get() else None
        try:
            result["k7b_fail_threshold"] = float(k7b_threshold_var.get())
        except ValueError:
            result["k7b_fail_threshold"] = 30.0  # unparsable entry -- fall back rather than crash
        result["k7_partc"] = k7c_status_var.get() if k7c_var.get() else None
        result["yearly_eligibility"] = elig_status_var.get() if elig_var.get() else None
        result["topper_list"] = topper_status_var.get() if topper_var.get() else None
        result["bright_weak"] = bw_status_var.get() if bw_var.get() else None
        try:
            result["bw_weak_threshold"] = float(bw_weak_threshold_var.get())
        except ValueError:
            result["bw_weak_threshold"] = 40.0  # unparsable entry -- fall back rather than crash
        try:
            result["bw_bright_threshold"] = float(bw_bright_threshold_var.get())
        except ValueError:
            result["bw_bright_threshold"] = 75.0  # unparsable entry -- fall back rather than crash
        root.destroy()

    ttk.Button(root, text="Generate", command=submit).pack(pady=14)
    root.protocol("WM_DELETE_WINDOW", submit)
    root.grab_set()
    root.wait_window()
    return result


def run_report_mode():
    """Build the PDF report(s) straight from the database -- no fetching, no
    captchas, no Excel involved. Asks (via a checkbox dialog) which
    report(s) to build and whether to include Regular students, EX
    students, or both in each: one semester-wise PDF per semester found
    in the database (e.g. First_Semester_Report.pdf, Second_Semester_
    Report.pdf), a cross-semester "Yearly_Result_Report.pdf" covering every
    enrollment across every semester/year it has data for, "K7_PartB_
    Report.pdf" (subject/THPRSLA-component/FASA-column statistics --
    lowest/highest/appeared/pass/above-60%/failed -- with one section per
    semester, each on its own page, empty/all-zero semesters skipped,
    and Failed % highlighted above the chosen threshold), "K7_PartC_
    Report.pdf" (the FA-TH vs SA-TH Score Index comparison, one row per
    Theory subject, Difference highlighted above 20%), and/or
    "Yearly_Eligible_NonEligible_Report.pdf" (the same Eligible/Non-
    Eligible-for-Next-Year call the Yearly Result report makes, pulled out as
    its own Sr.No./Enrollment No/Name/Program/Eligible-Non-Eligible list
    per academic year, Eligible enrollments listed before Not Eligible),
    and/or "Semesterwise_and_Yearly_Topper_List.pdf" (Top 5 by Percentage
    per semester, and Top 5 by average yearly Percentage per academic
    year among Eligible enrollments only -- see compute_topper_lists()),
    and/or "Semesterwise_Bright_Weak_Student_List.pdf" (per semester,
    Weak students -- Percentage below a user-chosen threshold -- listed
    first, then Bright students -- Percentage above a second user-chosen
    threshold -- in the same table, see compute_bright_weak_lists()).
    """
    if not os.path.exists(DB_FILE):
        print(f"Could not find {DB_FILE}. Run 'extract' mode at least once first to populate it.")
        return

    all_extracted, all_review = load_all_records_from_db(DB_FILE)
    student_records = [r for r in all_extracted if r["enrollment"] is not None]
    if not student_records:
        print(f"{DB_FILE} has no student data yet. Run 'extract' mode at least once first.")
        return

    semesters_in_db = sorted({r["semester_label"] for r in student_records},
                              key=lambda s: SEMESTER_NAMES.index(s) if s in SEMESTER_NAMES else 999)

    selection = ask_report_selection()
    if (selection["semester"] is None and selection["yearly_result"] is None
            and selection["k7_partb"] is None and selection["k7_partc"] is None
            and selection["yearly_eligibility"] is None and selection["topper_list"] is None
            and selection["bright_weak"] is None):
        print("No reports selected -- nothing to build.")
        return

    if selection["semester"] is not None:
        for sem_label in semesters_in_db:
            generate_semester_pdf(sem_label, DB_FILE, student_status=selection["semester"])

    blocked, gap_status = yearly_reports_are_blocked(DB_FILE)

    if selection["yearly_result"] is not None:
        if blocked:
            print("Yearly_Result_Report skipped -- " + (
                "run a Yearly Report Gap Check first (see Report mode in the web app)."
                if gap_status == "not_checked" else
                "missing-semester gaps are on record. Upload a secondary database to fill "
                "them (see Report mode in the web app) and re-run the Gap Check."
            ))
        else:
            generate_yearly_result_pdf(DB_FILE, student_status=selection["yearly_result"])

    if selection["k7_partb"] is not None:
        generate_k7_partb_pdf(DB_FILE, student_status=selection["k7_partb"], semesters=semesters_in_db,
                              fail_pct_threshold=selection["k7b_fail_threshold"])

    if selection["k7_partc"] is not None:
        generate_k7_partc_pdf(DB_FILE, student_status=selection["k7_partc"], semesters=semesters_in_db)

    if selection["yearly_eligibility"] is not None:
        if blocked:
            print("Yearly_Eligible_NonEligible_Report skipped -- " + (
                "run a Yearly Report Gap Check first (see Report mode in the web app)."
                if gap_status == "not_checked" else
                "missing-semester gaps are on record. Upload a secondary database to fill "
                "them (see Report mode in the web app) and re-run the Gap Check."
            ))
        else:
            generate_yearly_eligibility_pdf(DB_FILE, student_status=selection["yearly_eligibility"])

    if selection["topper_list"] is not None:
        generate_topper_list_pdf(DB_FILE, student_status=selection["topper_list"])

    if selection["bright_weak"] is not None:
        generate_bright_weak_pdf(DB_FILE, student_status=selection["bright_weak"],
                                 weak_threshold=selection["bw_weak_threshold"],
                                 bright_threshold=selection["bw_bright_threshold"])


# ==========================================================
# ENTRY POINT
# ==========================================================

if __name__ == "__main__":
    mode = sys.argv[1].lower() if len(sys.argv) > 1 else ""

    if mode == "train":
        run_train_mode()
    elif mode == "extract":
        run_extract_mode()
    elif mode == "report":
        run_report_mode()
    elif mode == "yearlyresult":
        if not os.path.exists(DB_FILE):
            print(f"Could not find {DB_FILE}. Run 'extract' mode at least once first to populate it.")
        else:
            generate_yearly_result_pdf(DB_FILE)
    elif mode == "k7partb":
        if not os.path.exists(DB_FILE):
            print(f"Could not find {DB_FILE}. Run 'extract' mode at least once first to populate it.")
        else:
            generate_k7_partb_pdf(DB_FILE)
    elif mode == "k7partc":
        if not os.path.exists(DB_FILE):
            print(f"Could not find {DB_FILE}. Run 'extract' mode at least once first to populate it.")
        else:
            generate_k7_partc_pdf(DB_FILE)
    elif mode == "eligibility":
        if not os.path.exists(DB_FILE):
            print(f"Could not find {DB_FILE}. Run 'extract' mode at least once first to populate it.")
        else:
            generate_yearly_eligibility_pdf(DB_FILE)
    elif mode == "toppers":
        if not os.path.exists(DB_FILE):
            print(f"Could not find {DB_FILE}. Run 'extract' mode at least once first to populate it.")
        else:
            generate_topper_list_pdf(DB_FILE)
    elif mode == "brightweak":
        if not os.path.exists(DB_FILE):
            print(f"Could not find {DB_FILE}. Run 'extract' mode at least once first to populate it.")
        else:
            generate_bright_weak_pdf(DB_FILE)
    elif mode == "recheck":
        run_recheck_mode()
    elif mode == "coursecodes":
        if not os.path.exists(DB_FILE):
            print(f"Could not find {DB_FILE}. Run 'train' mode at least once first to populate subjects.")
        else:
            run_course_code_entry_dialog(DB_FILE)
    else:
        print("Usage:")
        print("  python msbte_tool.py train        (one-time: teach it which rows to keep, per semester)")
        print("  python msbte_tool.py extract      (everyday: pull data for enrollment_list.txt)")
        print("  python msbte_tool.py recheck      (update marks/result for students who applied for rechecking)")
        print("  python msbte_tool.py report       (build the PDF report(s) from the database, no fetching)")
        print("  python msbte_tool.py yearlyresult (build just the cross-semester Yearly Result PDF)")
        print("  python msbte_tool.py k7partb      (build just the K7 (Part B) subject-statistics PDF, both statuses)")
        print("  python msbte_tool.py k7partc      (build just the K7 (Part C) FA/SA Score Index PDF, both statuses)")
        print("  python msbte_tool.py eligibility  (build just the Yearly Eligible/Non-Eligible Student List, both statuses)")
        print("  python msbte_tool.py toppers      (build just the Semesterwise and Yearly Topper List, both statuses)")
        print("  python msbte_tool.py brightweak   (build just the Semester wise Bright/Weak Student List, both statuses, weak<40%/bright>75%)")
        print("  python msbte_tool.py coursecodes  (enter Abbreviation/Course Code for each semester's subjects)")
