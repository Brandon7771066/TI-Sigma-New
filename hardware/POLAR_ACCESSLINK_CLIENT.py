"""
POLAR ACCESSLINK API CLIENT — T2-B Option A (Pass 12 ratified)
================================================================

Pulls Polar H10 RR-interval (HRV-grade) data from Polar Flow via the
official Polar AccessLink REST API. This is the "preferred path" per
the T2-B protocol because:
  1) it retroactively recovers the existing 7 sessions in
     data/polar_h10_export/ WITH RR intervals (the Flow JSON export
     has only HR summaries, no RR).
  2) zero hardware dependency from this Replit container.

ONE-TIME BRANDON SETUP STEPS (manual, ~10 min):
  1. Register a developer account at https://www.polar.com/accesslink-api/
     (free; need a working email + agree to terms)
  2. Create a new application in the Polar developer portal:
       - App name: TI Sigma Validation
       - Redirect URI: http://localhost:8080/callback
                       (we use the OOB / loopback flow)
  3. Copy client_id + client_secret from the portal.
  4. Add as Replit secrets:
       POLAR_CLIENT_ID
       POLAR_CLIENT_SECRET
  5. Run:  python hardware/POLAR_ACCESSLINK_CLIENT.py --auth
       This prints an authorization URL. Open it in a browser logged
       in to the same Polar account that owns the H10. Approve.
       The browser will redirect to localhost:8080/callback with a
       ?code=... query parameter. Paste that code back into the
       prompt. The script exchanges it for an access token + writes
       data/polar_accesslink/.token.json (chmod 600).
  6. Run:  python hardware/POLAR_ACCESSLINK_CLIENT.py --pull
       Pulls every available exercise / training session into
       data/polar_accesslink/<session_id>.json including RR samples.

Per #69 honesty: Brandon's account credentials are NOT in this script;
the OAuth flow is a one-time interactive step Brandon does himself.
The script handles only the technical glue.

Polar AccessLink docs: https://www.polar.com/accesslink-api/
"""
import argparse
import base64
import json
import os
import pathlib
import sys
import time
from urllib.parse import urlencode

import requests

POLAR_AUTH_URL  = "https://flow.polar.com/oauth2/authorization"
POLAR_TOKEN_URL = "https://polarremote.com/v2/oauth2/token"
POLAR_API_BASE  = "https://www.polaraccesslink.com/v3"
REDIRECT_URI    = "http://localhost:8080/callback"

DATA_DIR  = pathlib.Path("data/polar_accesslink")
TOKEN_FILE = DATA_DIR / ".token.json"


def _basic_auth_header():
    cid = os.environ.get("POLAR_CLIENT_ID")
    sec = os.environ.get("POLAR_CLIENT_SECRET")
    if not cid or not sec:
        sys.exit("ERROR: POLAR_CLIENT_ID and POLAR_CLIENT_SECRET must be set as Replit secrets.")
    creds = f"{cid}:{sec}".encode()
    return "Basic " + base64.b64encode(creds).decode()


def _bearer_header(token):
    return {"Authorization": f"Bearer {token}", "Accept": "application/json"}


def auth_flow():
    cid = os.environ.get("POLAR_CLIENT_ID")
    if not cid:
        sys.exit("ERROR: POLAR_CLIENT_ID must be set as a Replit secret.")
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    qs = urlencode({"response_type": "code", "client_id": cid,
                    "redirect_uri": REDIRECT_URI, "scope": "accesslink.read_all"})
    print("\n=== POLAR ACCESSLINK ONE-TIME AUTH ===\n")
    print("1. Open this URL in a browser logged in to your Polar account:\n")
    print(f"   {POLAR_AUTH_URL}?{qs}\n")
    print("2. Approve. You'll be redirected to localhost:8080/callback?code=...")
    print("3. Copy the value of the `code` query parameter.\n")
    code = input("Paste authorization code: ").strip()
    headers = {"Authorization": _basic_auth_header(),
               "Content-Type": "application/x-www-form-urlencoded",
               "Accept": "application/json"}
    body = {"grant_type": "authorization_code", "code": code,
            "redirect_uri": REDIRECT_URI}
    r = requests.post(POLAR_TOKEN_URL, headers=headers, data=body, timeout=20)
    r.raise_for_status()
    tok = r.json()
    # First-time access requires registering the user
    user_id = tok.get("x_user_id")
    access_token = tok["access_token"]
    if user_id:
        reg = requests.post(f"{POLAR_API_BASE}/users",
                            headers={**_bearer_header(access_token),
                                     "Content-Type": "application/json"},
                            json={"member-id": f"ti-sigma-{user_id}"}, timeout=20)
        if reg.status_code not in (200, 201, 409):  # 409 = already registered
            print(f"WARN: user-registration returned {reg.status_code}: {reg.text[:200]}")
    payload = {"access_token": access_token, "x_user_id": user_id,
               "issued_at": int(time.time())}
    TOKEN_FILE.write_text(json.dumps(payload, indent=2))
    os.chmod(TOKEN_FILE, 0o600)
    print(f"\n✅ Token saved to {TOKEN_FILE} (chmod 600).")
    print(f"   user_id={user_id}.  Now run: python {sys.argv[0]} --pull")


def _load_token():
    if not TOKEN_FILE.exists():
        sys.exit(f"ERROR: {TOKEN_FILE} missing. Run with --auth first.")
    return json.loads(TOKEN_FILE.read_text())


def pull_sessions():
    tok = _load_token()
    h = _bearer_header(tok["access_token"])
    DATA_DIR.mkdir(parents=True, exist_ok=True)

    # Step 1: create transaction (Polar's "give me what's new" pattern)
    r = requests.post(f"{POLAR_API_BASE}/users/{tok['x_user_id']}/exercise-transactions",
                      headers=h, timeout=20)
    if r.status_code == 204:
        print("No new exercises since last pull. Try the AccessLink Polar Flow web UI to verify.")
        return
    r.raise_for_status()
    tx = r.json()
    tx_id = tx["transaction-id"]
    print(f"Transaction {tx_id} opened.")

    # Step 2: list exercise URLs
    r = requests.get(tx["resource-uri"], headers=h, timeout=20)
    r.raise_for_status()
    urls = r.json().get("exercises", [])
    print(f"  {len(urls)} new exercises.")

    saved = 0
    for url in urls:
        r = requests.get(url, headers=h, timeout=30)
        r.raise_for_status()
        ex = r.json()
        # Step 3: pull HR samples
        hr_url = url + "/samples/heart-rate"
        rr_url = url + "/samples/rr"
        try:
            hr = requests.get(hr_url, headers=h, timeout=30).json()
        except Exception:
            hr = None
        try:
            rr = requests.get(rr_url, headers=h, timeout=30).json()
        except Exception:
            rr = None
        ex_id = ex.get("id", url.rsplit("/", 1)[-1])
        out = {"summary": ex, "hr_samples": hr, "rr_samples": rr,
               "pulled_at": int(time.time())}
        fname = DATA_DIR / f"{ex_id}.json"
        fname.write_text(json.dumps(out, indent=2))
        saved += 1
        print(f"  saved {fname.name}  RR={'yes' if rr else 'no'}")

    # Step 4: commit transaction
    r = requests.put(tx["resource-uri"], headers=h, timeout=20)
    print(f"Transaction committed. Saved {saved} sessions to {DATA_DIR}/")


def main():
    ap = argparse.ArgumentParser(description="Polar AccessLink API client (T2-B Option A)")
    g = ap.add_mutually_exclusive_group(required=True)
    g.add_argument("--auth", action="store_true", help="One-time OAuth flow")
    g.add_argument("--pull", action="store_true", help="Pull new exercises with RR data")
    args = ap.parse_args()
    if args.auth: auth_flow()
    elif args.pull: pull_sessions()


if __name__ == "__main__":
    main()
