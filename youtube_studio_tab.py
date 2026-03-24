"""
YouTube Studio Tab — TI Sigma Research Channel
================================================
Streamlit tab for managing the entire video pipeline:
  - OAuth setup (one-time)
  - Script generation
  - Video production (FFmpeg + OpenAI TTS)
  - YouTube upload
  - Channel dashboard
"""

import os
import json
import time
import threading
from pathlib import Path
from typing import Optional, Dict, Any

import streamlit as st

from ti_video_engine import (
    VIDEO_CATALOGUE,
    VIDEO_DIR,
    THUMB_DIR,
    SCRIPT_DIR,
    produce_urb_video,
    load_script,
    save_script,
    generate_script,
)
from youtube_uploader import (
    credentials_configured,
    is_authorized,
    get_auth_url,
    exchange_code,
    upload_video,
    get_channel_info,
    list_recent_uploads,
)

# ─────────────────────────────────────────────────────────────────────────────
# PAPER REGISTRY — all URBs with known paper files
# ─────────────────────────────────────────────────────────────────────────────

PAPER_REGISTRY = {
    509: "papers/URB_TI_SIGMA_THEORY_OF_CONTRADICTIONS_509.md",
    508: "papers/URB_BENGSTON_WATER_QUARTZ_508.md",
    507: "papers/URB_MINIMAL_OPERATIONS_507.md",
    506: "papers/URB_I_COMPLETENESS_506.md",
    505: "papers/URB_UNIFIED_TELEKINESIS_505.md",
    504: "papers/URB_TELEKINESIS_FORMULA_504.md",
    503: "papers/URB_ONTOGENY_COSMOGONY_503.md",
    502: "papers/URB_LOVE_GENESIS_502.md",
    501: "papers/URB_LOVE_PRIMACY_501.md",
    500: "papers/URB_BOK_CLOSURE_500.md",
    499: "papers/URB_MAHARISHI_499.md",
}


def _paper_exists(urb_num: int) -> bool:
    path = PAPER_REGISTRY.get(urb_num, "")
    return Path(path).exists() if path else False


def _mp4_exists(urb_num: int) -> bool:
    return (VIDEO_DIR / f"urb_{urb_num}.mp4").exists()


def _script_exists(urb_num: int) -> bool:
    return (SCRIPT_DIR / f"urb_{urb_num}_script.json").exists()


def _thumb_exists(urb_num: int) -> bool:
    return (THUMB_DIR / f"urb_{urb_num}_thumb.png").exists()


def _uploaded_key(urb_num: int) -> str:
    return f"yt_uploaded_urb_{urb_num}"


def _mark_uploaded(urb_num: int, url: str):
    """Persist upload URL in a simple JSON log."""
    log_file = Path(".local/youtube_uploads.json")
    log_file.parent.mkdir(parents=True, exist_ok=True)
    data = {}
    if log_file.exists():
        try:
            data = json.loads(log_file.read_text())
        except Exception:
            data = {}
    data[str(urb_num)] = {"url": url, "ts": time.strftime("%Y-%m-%d %H:%M")}
    log_file.write_text(json.dumps(data, indent=2))


def _get_uploaded_log() -> Dict:
    log_file = Path(".local/youtube_uploads.json")
    if log_file.exists():
        try:
            return json.loads(log_file.read_text())
        except Exception:
            pass
    return {}


# ─────────────────────────────────────────────────────────────────────────────
# SECTION: OAuth Setup
# ─────────────────────────────────────────────────────────────────────────────

def _render_oauth_setup():
    st.subheader("🔐 YouTube Authorization")

    if not credentials_configured():
        st.error(
            "YouTube API credentials not found. "
            "Add **YOUTUBE_CLIENT_ID** and **YOUTUBE_CLIENT_SECRET** as Replit secrets."
        )
        with st.expander("📋 How to set up YouTube API credentials (5 min, one-time)"):
            st.markdown("""
**Step 1 — Google Cloud Console**
1. Go to [console.cloud.google.com](https://console.cloud.google.com)
2. Create a new project (name it anything, e.g. "TI Sigma YouTube")
3. In the left menu → **APIs & Services** → **Library**
4. Search for **"YouTube Data API v3"** → click it → **Enable**

**Step 2 — OAuth Credentials**
1. Go to **APIs & Services** → **Credentials**
2. Click **+ Create Credentials** → **OAuth client ID**
3. Application type: **Desktop app**
4. Name: "TI Sigma Uploader" → **Create**
5. Copy the **Client ID** and **Client Secret** shown

**Step 3 — Replit Secrets**
1. In Replit, open **Secrets** (lock icon in sidebar)
2. Add `YOUTUBE_CLIENT_ID` → paste Client ID
3. Add `YOUTUBE_CLIENT_SECRET` → paste Client Secret
4. Restart the app

**Step 4 — OAuth Consent Screen** (if you get an error)
1. **APIs & Services** → **OAuth consent screen**
2. User type: **External** → **Create**
3. App name: "TI Sigma" → your email → **Save**
4. Add yourself as a **Test User**
            """)
        return False

    if is_authorized():
        st.success("✅ YouTube channel authorized and ready.")
        info = get_channel_info()
        if info:
            col1, col2, col3 = st.columns(3)
            col1.metric("Channel", info["title"])
            col2.metric("Subscribers", f"{int(info['subscribers']):,}")
            col3.metric("Total Views", f"{int(info['total_views']):,}")
            st.caption(f"[Open channel]({info['url']})")
        if st.button("🔄 Re-authorize (if token expired)"):
            Path(".local/youtube_token.pkl").unlink(missing_ok=True)
            st.rerun()
        return True

    # Not yet authorized
    st.info("Credentials found. Click below to authorize your YouTube channel.")
    auth_url = get_auth_url()
    if auth_url:
        st.markdown(f"**Step 1:** [Click here to authorize Google/YouTube]({auth_url})")
        st.markdown("**Step 2:** Copy the code Google gives you and paste it below.")
        code = st.text_input("Authorization code:", key="yt_oauth_code")
        if st.button("✅ Complete Authorization"):
            if code.strip():
                ok = exchange_code(code.strip())
                if ok:
                    st.success("Authorization successful! Reloading...")
                    time.sleep(1)
                    st.rerun()
                else:
                    st.error("Authorization failed. Check the code and try again.")
            else:
                st.warning("Paste the authorization code first.")
    return False


# ─────────────────────────────────────────────────────────────────────────────
# SECTION: Video Queue
# ─────────────────────────────────────────────────────────────────────────────

def _render_video_queue(authorized: bool):
    st.subheader("🎬 Video Production Queue")

    upload_log = _get_uploaded_log()

    priority_urbs = [509, 507, 506, 505, 502, 500, 508, 504, 503, 501, 499]

    for urb_num in priority_urbs:
        cat = VIDEO_CATALOGUE.get(urb_num, {})
        title = cat.get("title", f"URB #{urb_num}")
        uploaded_info = upload_log.get(str(urb_num))

        # Status badges
        has_paper  = _paper_exists(urb_num)
        has_script = _script_exists(urb_num)
        has_mp4    = _mp4_exists(urb_num)
        has_thumb  = _thumb_exists(urb_num)
        is_live    = uploaded_info is not None

        status_icon = "🟢" if is_live else "🟡" if has_mp4 else "🔵" if has_script else "⚪"

        with st.expander(f"{status_icon} URB #{urb_num} — {title}", expanded=False):
            col_a, col_b, col_c = st.columns([2, 1, 1])

            with col_a:
                if cat.get("hook"):
                    st.caption(f'_"{cat["hook"]}"_')
                if cat.get("tags"):
                    st.caption("Tags: " + ", ".join(cat["tags"][:5]))

            with col_b:
                st.markdown(
                    f"📄 Paper: {'✅' if has_paper else '❌'}  \n"
                    f"📝 Script: {'✅' if has_script else '❌'}  \n"
                    f"🎬 Video: {'✅' if has_mp4 else '❌'}  \n"
                    f"🖼️ Thumb: {'✅' if has_thumb else '❌'}  \n"
                    f"📺 Live: {'✅' if is_live else '❌'}"
                )

            with col_c:
                if is_live:
                    st.success(f"Live!")
                    st.markdown(f"[Watch]({uploaded_info['url']})")

            st.divider()

            # Script actions
            scol1, scol2 = st.columns(2)
            with scol1:
                if st.button(
                    f"📝 {'Regenerate' if has_script else 'Generate'} Script",
                    key=f"script_{urb_num}",
                    disabled=not has_paper,
                    help="Requires paper file" if not has_paper else None,
                ):
                    with st.spinner("Generating script with AI…"):
                        paper_path = PAPER_REGISTRY.get(urb_num, "")
                        data = generate_script(paper_path, urb_num=urb_num)
                        save_script(data, urb_num)
                    st.success("Script generated!")
                    st.rerun()

            with scol2:
                if has_script:
                    script_data = load_script(urb_num)
                    if script_data:
                        st.caption(f"Title: {script_data.get('youtube_title', '')[:60]}")

            # Show script content if exists
            if has_script:
                with st.container():
                    script_data = load_script(urb_num)
                    if script_data and st.checkbox(f"Preview script", key=f"show_script_{urb_num}"):
                        for seg in script_data.get("segments", []):
                            st.markdown(f"**{seg.get('label','?')}** _{seg.get('visual_note','')}:_")
                            st.markdown(f"> {seg.get('script', '')[:300]}")

            st.divider()

            # Produce video
            produce_disabled = not has_paper and not has_script
            if st.button(
                f"🎬 {'Reproduce' if has_mp4 else 'Produce'} Video",
                key=f"produce_{urb_num}",
                disabled=produce_disabled,
                type="primary" if (has_script and not has_mp4) else "secondary",
            ):
                paper_path = PAPER_REGISTRY.get(urb_num, "")
                if not paper_path:
                    paper_path = ""

                progress_bar = st.progress(0, text="Starting…")

                def _cb(msg, pct):
                    progress_bar.progress(min(pct, 100) / 100, text=msg)

                result = produce_urb_video(
                    paper_path, urb_num=urb_num,
                    progress_callback=_cb
                )
                if result["status"] == "success":
                    st.success(f"✅ Video ready! {result['size_mb']} MB")
                    st.rerun()
                else:
                    st.error(f"Video production failed: {result.get('reason')}")

            # Preview / download if video exists
            if has_mp4:
                mp4_path = str(VIDEO_DIR / f"urb_{urb_num}.mp4")
                with open(mp4_path, "rb") as f:
                    st.download_button(
                        "⬇️ Download MP4",
                        data=f,
                        file_name=f"TISigma_URB{urb_num}.mp4",
                        mime="video/mp4",
                        key=f"dl_{urb_num}",
                    )

            if has_thumb:
                thumb_path = str(THUMB_DIR / f"urb_{urb_num}_thumb.png")
                st.image(thumb_path, caption="Thumbnail", use_container_width=False, width=360)
                with open(thumb_path, "rb") as f:
                    st.download_button(
                        "⬇️ Download Thumbnail",
                        data=f,
                        file_name=f"TISigma_URB{urb_num}_thumb.png",
                        mime="image/png",
                        key=f"dlt_{urb_num}",
                    )

            st.divider()

            # Upload to YouTube
            if has_mp4 and authorized and not is_live:
                script_data = load_script(urb_num) or {}
                cat = VIDEO_CATALOGUE.get(urb_num, {})
                default_title = cat.get("title", script_data.get("youtube_title", f"URB #{urb_num}"))
                default_desc  = cat.get("description_template", script_data.get("youtube_description", ""))
                default_tags  = cat.get("tags", script_data.get("tags", []))

                with st.form(key=f"upload_form_{urb_num}"):
                    st.markdown("**Upload to YouTube**")
                    upload_title = st.text_input("Title", value=default_title[:100], key=f"ut_{urb_num}")
                    upload_desc  = st.text_area("Description", value=default_desc[:1000], height=120, key=f"ud_{urb_num}")
                    upload_tags  = st.text_input("Tags (comma-separated)", value=", ".join(default_tags[:10]), key=f"utg_{urb_num}")
                    privacy_sel  = st.selectbox("Privacy", ["public", "unlisted", "private"], key=f"up_{urb_num}")
                    submitted = st.form_submit_button("📺 Upload to YouTube", type="primary")

                    if submitted:
                        mp4_path   = str(VIDEO_DIR / f"urb_{urb_num}.mp4")
                        thumb_path = str(THUMB_DIR / f"urb_{urb_num}_thumb.png") if has_thumb else None
                        tags_list  = [t.strip() for t in upload_tags.split(",") if t.strip()]

                        with st.spinner("Uploading to YouTube… (this may take a few minutes)"):
                            result = upload_video(
                                video_path=mp4_path,
                                title=upload_title,
                                description=upload_desc,
                                tags=tags_list,
                                thumbnail_path=thumb_path,
                                privacy_status=privacy_sel,
                            )

                        if result["status"] == "success":
                            _mark_uploaded(urb_num, result["url"])
                            st.success(f"🎉 Uploaded! {result['url']}")
                            st.balloons()
                            st.rerun()
                        else:
                            st.error(f"Upload failed: {result.get('reason')}")

            elif has_mp4 and not authorized:
                st.info("Authorize YouTube above to enable one-click upload.")

            elif is_live:
                st.success(f"✅ Published {uploaded_info['ts']} → [Watch on YouTube]({uploaded_info['url']})")


# ─────────────────────────────────────────────────────────────────────────────
# SECTION: Batch Controls
# ─────────────────────────────────────────────────────────────────────────────

def _render_batch_controls(authorized: bool):
    st.subheader("⚡ Batch Operations")

    col1, col2, col3 = st.columns(3)

    with col1:
        st.markdown("**Generate all missing scripts**")
        if st.button("📝 Generate All Scripts", key="batch_scripts"):
            progress = st.progress(0, text="Generating scripts…")
            urbs_with_papers = [u for u in PAPER_REGISTRY if _paper_exists(u) and not _script_exists(u)]
            if not urbs_with_papers:
                st.info("All scripts already generated.")
            else:
                for i, urb_num in enumerate(urbs_with_papers):
                    progress.progress((i + 1) / len(urbs_with_papers),
                                      text=f"Generating URB #{urb_num}…")
                    paper_path = PAPER_REGISTRY[urb_num]
                    data = generate_script(paper_path, urb_num=urb_num)
                    save_script(data, urb_num)
                st.success(f"Generated {len(urbs_with_papers)} scripts!")

    with col2:
        st.markdown("**Produce all missing videos**")
        st.caption("⚠️ This takes ~5-10 min per video (OpenAI TTS + FFmpeg)")
        ready_to_produce = [u for u in PAPER_REGISTRY if _script_exists(u) and not _mp4_exists(u)]
        st.caption(f"{len(ready_to_produce)} videos ready to produce")
        if st.button("🎬 Produce All Videos", key="batch_produce",
                     disabled=not ready_to_produce):
            for urb_num in ready_to_produce:
                with st.spinner(f"Producing URB #{urb_num}…"):
                    result = produce_urb_video(PAPER_REGISTRY[urb_num], urb_num=urb_num)
                    if result["status"] == "success":
                        st.success(f"URB #{urb_num} done — {result['size_mb']} MB")
                    else:
                        st.error(f"URB #{urb_num} failed: {result.get('reason')}")

    with col3:
        st.markdown("**Recent YouTube uploads**")
        if authorized:
            if st.button("🔄 Refresh upload list", key="refresh_yt"):
                st.session_state["recent_uploads"] = list_recent_uploads(10)
        else:
            st.caption("Authorize YouTube to see channel uploads.")

    # Show recent uploads
    if authorized and "recent_uploads" in st.session_state:
        uploads = st.session_state["recent_uploads"]
        if uploads:
            st.markdown("**Recent uploads on channel:**")
            for v in uploads:
                st.markdown(f"- [{v['title']}]({v['url']}) — {v['published'][:10]}")
        else:
            st.info("No uploads found on channel.")


# ─────────────────────────────────────────────────────────────────────────────
# SECTION: Channel Stats
# ─────────────────────────────────────────────────────────────────────────────

def _render_channel_stats(authorized: bool):
    if not authorized:
        return

    st.subheader("📊 Channel Overview")
    info = get_channel_info()
    if info:
        c1, c2, c3, c4 = st.columns(4)
        c1.metric("Channel", info["title"])
        c2.metric("Subscribers", f"{int(info['subscribers']):,}")
        c3.metric("Total Views", f"{int(info['total_views']):,}")
        c4.metric("Videos", info["video_count"])
    else:
        st.caption("Could not fetch channel info.")


# ─────────────────────────────────────────────────────────────────────────────
# SECTION: Canva Thumbnail Tips
# ─────────────────────────────────────────────────────────────────────────────

def _render_canva_tips():
    with st.expander("🎨 Canva Thumbnail Workflow (optional polish)", expanded=False):
        st.markdown("""
The pipeline auto-generates a thumbnail PNG for every video.
For extra polish, here's the workflow with your Canva subscription:

1. Download the auto-generated thumbnail PNG (above each video)
2. In Canva → New Design → YouTube Thumbnail (1280×720)
3. Upload the PNG as a background layer
4. Overlay bold text, your face photo, or Canva elements on top
5. Export → Download → use during YouTube upload (or the app uploads the auto-generated one)

**Why this works:** The auto-thumbnail has the right colors, URB number badge, and title text.
Canva adds your personal brand (face, style elements) in minutes — no design skills needed.

**One-click option:** Just leave it — the auto-generated thumbnail is perfectly serviceable
and the app uploads it automatically alongside your video.
        """)


# ─────────────────────────────────────────────────────────────────────────────
# MAIN TAB RENDERER
# ─────────────────────────────────────────────────────────────────────────────

def render_youtube_studio_tab():
    st.header("📺 YouTube Studio — TI Sigma Research Channel")
    st.caption(
        "Full automation: paper → script → video → upload. "
        "One-time YouTube authorization required."
    )

    # Tabs within the tab
    sub = st.tabs(["🔐 Setup & Auth", "🎬 Video Queue", "⚡ Batch", "📊 Channel"])

    with sub[0]:
        authorized = _render_oauth_setup()
        _render_canva_tips()
        st.session_state["yt_authorized"] = authorized

    authorized = st.session_state.get("yt_authorized", False)

    with sub[1]:
        _render_video_queue(authorized)

    with sub[2]:
        _render_batch_controls(authorized)

    with sub[3]:
        _render_channel_stats(authorized)
