"""Spotify AA-2 path — 30-second-preview acquisition for ETM-1 Phase-2 baseline songs.

Per Pass-77-B8 §1.2 Brandon directive "Use Spotify".

REQUIREMENTS:
    - spotipy (`uv add spotipy` if missing)
    - SPOTIPY_CLIENT_ID + SPOTIPY_CLIENT_SECRET env vars
      (Brandon: get free creds at https://developer.spotify.com/dashboard,
       2-minute self-service signup, no credit card)
    - then `python analyses/etm1_phase2_mir/spotify_audio_acquisition.py`

HONEST #69 (per paper §1.2.1):
    Spotify previews are 30 seconds. 6 of 9 ETM-1 v2 features extract usefully
    from 30s (TRD/HS/SFD/LTS/VCM/GMP/VSF/CRA + partial DAM).
    3 of 9 are degraded or lost on 30s samples:
      - MCC (motif circularity) — needs first-N-vs-last-N seconds, 30s has no "closure"
      - AKM (ascending modulation) — full songs have 3-5 modulations; 30s has 0-1
      - TEI (tag-ending intensification) — tag-endings live in song's final 30-60s,
        not in the hook/middle that Spotify previews are usually drawn from
    For maximum fidelity: Brandon supplements with owned MP3s for these 3 features
    (z-1-b carry).

LATE-2024 API CHANGE:
    Spotify deprecated `preview_url` for many newly-added tracks.
    Existing Gaither + PMD-Sky catalogue likely still has preview URLs.
    Script logs `preview_url_available: bool` per song and reports coverage at end.
"""
from __future__ import annotations
import json, os, sys, re, time
from pathlib import Path

try:
    import spotipy
    from spotipy.oauth2 import SpotifyClientCredentials
except ImportError:
    print("spotipy not installed. Run: uv add spotipy", file=sys.stderr)
    sys.exit(2)

try:
    import requests
except ImportError:
    print("requests missing (unexpected); run: uv add requests", file=sys.stderr)
    sys.exit(2)

OUT_DIR = Path(__file__).parent / "audio"
MANIFEST_PATH = OUT_DIR / "_spotify_acquisition_manifest.json"

# 10 Phase-1-baseline songs (Pass-77-B9 BRANDON-CANONICAL GVB top-5 + PMD-Sky top-5)
# Honest #69: B7's agent-nominated GVB list was SUPERSEDED by Brandon-canonical list B9.
# Prior agent-picks acquired as SECONDARY_COMPARISON below.
SONGS = [
    {"slug": "gaither_clean",
     "query": "Clean", "artist": "Gaither Vocal Band"},
    {"slug": "gaither_the_time_i_must_sing",
     "query": "The Time I Must Sing", "artist": "Gaither Vocal Band"},
    {"slug": "gaither_god_gave_the_song",
     "query": "God Gave the Song", "artist": "Gaither Vocal Band"},
    {"slug": "gaither_he_touched_me",
     "query": "He Touched Me", "artist": "Gaither Vocal Band"},
    {"slug": "gaither_i_just_want_to_thank_you_lord",
     "query": "I Just Want to Thank You Lord", "artist": "Gaither Vocal Band"},
    {"slug": "pmd_dont_ever_forget",
     "query": "Don't Ever Forget", "artist": "Pokémon Mystery Dungeon Explorers of Sky"},
    {"slug": "pmd_heartbeat_heartbreak",
     "query": "Heartbeat Heartbreak", "artist": "Pokémon Mystery Dungeon"},
    {"slug": "pmd_through_the_sea_of_time",
     "query": "Through the Sea of Time", "artist": "Pokémon Mystery Dungeon"},
    {"slug": "pmd_dialgas_fight_to_the_finish",
     "query": "Dialga's Fight to the Finish", "artist": "Pokémon Mystery Dungeon"},
    {"slug": "pmd_in_the_hands_of_fate",
     "query": "In the Hands of Fate", "artist": "Pokémon Mystery Dungeon"},
]

# Rap control set (Pass-77-B8 §1.3; agent-nominated; Brandon-veto-able z-4-a)
RAP_CONTROLS = [
    {"slug": "rap_control_wap_cardi_b",
     "query": "WAP", "artist": "Cardi B"},
    {"slug": "rap_control_mask_off_future",
     "query": "Mask Off", "artist": "Future"},
    {"slug": "rap_control_ny_state_of_mind_nas",
     "query": "N.Y. State of Mind", "artist": "Nas"},
    {"slug": "rap_control_dna_kendrick",
     "query": "DNA", "artist": "Kendrick Lamar"},
    {"slug": "rap_control_dior_pop_smoke",
     "query": "Dior", "artist": "Pop Smoke"},
]

# Pass-77-B9 secondary-comparison: agent's prior-nominated GVB picks (NOT in Brandon-canonical-5)
# Acquired to test agent's intuition partial-vs-zero calibration on Gaither catalogue
SECONDARY_COMPARISON_AGENT_PRIOR_GVB = [
    {"slug": "gaither_secondary_i_bowed_on_my_knees",
     "query": "I Bowed on My Knees and Cried Holy", "artist": "Gaither Vocal Band"},
    {"slug": "gaither_secondary_alpha_and_omega",
     "query": "Alpha and Omega", "artist": "Gaither Vocal Band"},
    {"slug": "gaither_secondary_then_came_the_morning",
     "query": "Then Came the Morning", "artist": "Gaither Vocal Band"},
    {"slug": "gaither_secondary_because_he_lives_live",
     "query": "Because He Lives (Live)", "artist": "Gaither Vocal Band"},
    {"slug": "gaither_secondary_it_is_well_with_my_soul",
     "query": "It Is Well with My Soul", "artist": "Gaither Vocal Band"},
]

ALL_TARGETS = SONGS + RAP_CONTROLS + SECONDARY_COMPARISON_AGENT_PRIOR_GVB


def get_client():
    cid = os.environ.get("SPOTIPY_CLIENT_ID")
    csec = os.environ.get("SPOTIPY_CLIENT_SECRET")
    if not cid or not csec:
        print("ERROR: SPOTIPY_CLIENT_ID and SPOTIPY_CLIENT_SECRET env vars required.",
              file=sys.stderr)
        print("Brandon: get free creds at https://developer.spotify.com/dashboard",
              file=sys.stderr)
        sys.exit(3)
    auth = SpotifyClientCredentials(client_id=cid, client_secret=csec)
    return spotipy.Spotify(auth_manager=auth)


def search_track(sp, query: str, artist: str) -> dict | None:
    q = f'track:"{query}" artist:"{artist}"'
    try:
        res = sp.search(q=q, type="track", limit=5)
    except Exception as e:
        return {"_error": repr(e)}
    items = res.get("tracks", {}).get("items", [])
    if not items:
        # Fallback: looser query
        res = sp.search(q=f"{query} {artist}", type="track", limit=5)
        items = res.get("tracks", {}).get("items", [])
    if not items:
        return None
    return items[0]


def download_preview(url: str, dest: Path) -> bool:
    try:
        r = requests.get(url, timeout=30)
        r.raise_for_status()
        dest.write_bytes(r.content)
        return True
    except Exception as e:
        print(f"  download failed: {e!r}", file=sys.stderr)
        return False


def main():
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    sp = get_client()
    manifest = {
        "schema_version": "1.0-Pass77B8-2026-05-26",
        "acquisition_path": "AA-2 Spotify 30s preview",
        "honest_69_30s_limitation_note": "MCC + AKM + TEI features degraded; see paper §1.2.1",
        "results": [],
    }
    n_found = n_preview = n_downloaded = 0
    for t in ALL_TARGETS:
        print(f"[{t['slug']}]")
        time.sleep(0.3)  # gentle rate limit
        track = search_track(sp, t["query"], t["artist"])
        rec = {"slug": t["slug"], "query": t["query"], "artist_query": t["artist"]}
        if track is None or "_error" in (track or {}):
            rec["status"] = "not_found"
            if track and "_error" in track:
                rec["error"] = track["_error"]
            print(f"  NOT FOUND")
            manifest["results"].append(rec)
            continue
        n_found += 1
        rec["spotify_track_id"] = track["id"]
        rec["track_name"] = track["name"]
        rec["track_artists"] = [a["name"] for a in track["artists"]]
        rec["full_duration_ms"] = track["duration_ms"]
        rec["album"] = track["album"]["name"]
        preview_url = track.get("preview_url")
        rec["preview_url_available"] = preview_url is not None
        if preview_url:
            n_preview += 1
            dest = OUT_DIR / f"{t['slug']}.mp3"
            ok = download_preview(preview_url, dest)
            rec["preview_downloaded_to"] = str(dest) if ok else None
            if ok:
                n_downloaded += 1
                print(f"  OK -> {dest.name} (30s, {dest.stat().st_size} bytes)")
            else:
                print(f"  download FAILED")
        else:
            rec["preview_downloaded_to"] = None
            print(f"  NO PREVIEW URL (Spotify late-2024 deprecation; track found but unplayable)")
        manifest["results"].append(rec)

    manifest["_summary"] = {
        "total_targets": len(ALL_TARGETS),
        "n_found": n_found,
        "n_preview_url_available": n_preview,
        "n_downloaded": n_downloaded,
    }
    with open(MANIFEST_PATH, "w") as h:
        json.dump(manifest, h, indent=2)
    print(f"\nManifest -> {MANIFEST_PATH}")
    print(f"Found: {n_found}/{len(ALL_TARGETS)} | Preview URL available: {n_preview} | Downloaded: {n_downloaded}")


if __name__ == "__main__":
    main()
