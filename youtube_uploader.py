"""
YouTube Uploader — TI Sigma Research Channel
=============================================
Handles OAuth 2.0 authentication and video upload to YouTube.

Setup (one-time):
  1. Google Cloud Console → Enable YouTube Data API v3
  2. Create OAuth 2.0 credentials (Desktop app type)
  3. Store YOUTUBE_CLIENT_ID + YOUTUBE_CLIENT_SECRET as Replit secrets
  4. Call authorize_youtube() once → stores refresh token as secret

After setup: upload_video() is fully automatic.
"""

import os
import json
import time
import pickle
import tempfile
from pathlib import Path
from typing import Optional, Dict, Any

# Check whether Google API libraries are installed
try:
    import google.auth  # noqa: F401
    GOOGLE_LIBS_AVAILABLE = True
except ImportError:
    GOOGLE_LIBS_AVAILABLE = False

# ─────────────────────────────────────────────────────────────────────────────
# CONFIGURATION
# ─────────────────────────────────────────────────────────────────────────────

SCOPES = ["https://www.googleapis.com/auth/youtube.upload",
          "https://www.googleapis.com/auth/youtube"]

TOKEN_FILE = ".local/youtube_token.pkl"  # stored locally after first auth
CREDS_FILE = ".local/youtube_client_secrets.json"  # optional: paste full JSON

CHANNEL_DEFAULTS = {
    "category_id": "27",        # Education
    "default_language": "en",
    "privacy_status": "public", # or "private" for review first
}

# ─────────────────────────────────────────────────────────────────────────────
# CREDENTIALS
# ─────────────────────────────────────────────────────────────────────────────

def _get_client_config() -> Optional[Dict]:
    """Build OAuth client config from env or secrets file."""
    # Try full JSON file first (user can paste the downloaded JSON)
    if Path(CREDS_FILE).exists():
        with open(CREDS_FILE) as f:
            return json.load(f)

    client_id     = os.environ.get("YOUTUBE_CLIENT_ID", "")
    client_secret = os.environ.get("YOUTUBE_CLIENT_SECRET", "")

    if not client_id or not client_secret:
        return None

    return {
        "installed": {
            "client_id": client_id,
            "client_secret": client_secret,
            "auth_uri": "https://accounts.google.com/o/oauth2/auth",
            "token_uri": "https://oauth2.googleapis.com/token",
            "redirect_uris": ["urn:ietf:wg:oauth:2.0:oob", "http://localhost"]
        }
    }


def credentials_configured() -> bool:
    """Return True if OAuth client credentials exist."""
    if not GOOGLE_LIBS_AVAILABLE:
        return False
    return _get_client_config() is not None


def is_authorized() -> bool:
    """Return True if we have a valid (or refreshable) token stored."""
    return Path(TOKEN_FILE).exists()


def get_credentials():
    """Load stored credentials, refreshing if expired."""
    if not GOOGLE_LIBS_AVAILABLE:
        return None
    from google.oauth2.credentials import Credentials
    from google.auth.transport.requests import Request

    if not Path(TOKEN_FILE).exists():
        return None

    with open(TOKEN_FILE, "rb") as f:
        creds = pickle.load(f)

    if creds and creds.expired and creds.refresh_token:
        try:
            creds.refresh(Request())
            with open(TOKEN_FILE, "wb") as f:
                pickle.dump(creds, f)
        except Exception:
            return None

    return creds if (creds and creds.valid) else None


# ─────────────────────────────────────────────────────────────────────────────
# AUTHORIZATION FLOW
# ─────────────────────────────────────────────────────────────────────────────

def get_auth_url() -> Optional[str]:
    """
    Return the Google OAuth authorization URL.
    User visits this URL, approves, then pastes the code back.
    """
    if not GOOGLE_LIBS_AVAILABLE:
        return None
    from google_auth_oauthlib.flow import Flow

    config = _get_client_config()
    if not config:
        return None

    flow = Flow.from_client_config(config, scopes=SCOPES)
    flow.redirect_uri = "urn:ietf:wg:oauth:2.0:oob"

    auth_url, _ = flow.authorization_url(
        access_type="offline",
        include_granted_scopes="true",
        prompt="consent"
    )
    return auth_url


def exchange_code(code: str) -> bool:
    """
    Exchange authorization code for credentials and store them.
    Returns True on success.
    """
    if not GOOGLE_LIBS_AVAILABLE:
        return False
    from google_auth_oauthlib.flow import Flow

    config = _get_client_config()
    if not config:
        return False

    try:
        flow = Flow.from_client_config(config, scopes=SCOPES)
        flow.redirect_uri = "urn:ietf:wg:oauth:2.0:oob"
        flow.fetch_token(code=code.strip())
        creds = flow.credentials

        Path(TOKEN_FILE).parent.mkdir(parents=True, exist_ok=True)
        with open(TOKEN_FILE, "wb") as f:
            pickle.dump(creds, f)
        return True
    except Exception as e:
        print(f"[YouTube] Token exchange failed: {e}")
        return False


# ─────────────────────────────────────────────────────────────────────────────
# VIDEO UPLOAD
# ─────────────────────────────────────────────────────────────────────────────

def upload_video(  # noqa: C901
    video_path: str,
    title: str,
    description: str,
    tags: list[str] = None,
    thumbnail_path: str = None,
    privacy_status: str = "public",
    category_id: str = "27",
    playlist_id: str = None,
    notify_subscribers: bool = True,
) -> Dict[str, Any]:
    """
    Upload a video to YouTube.

    Returns dict with keys:
      status: "success" | "error"
      video_id: YouTube video ID (on success)
      url: full YouTube URL (on success)
      reason: error description (on error)
    """
    from googleapiclient.discovery import build
    from googleapiclient.http import MediaFileUpload
    from google.auth.transport.requests import Request

    creds = get_credentials()
    if not creds:
        return {"status": "error", "reason": "Not authorized. Complete OAuth setup first."}

    if not Path(video_path).exists():
        return {"status": "error", "reason": f"Video file not found: {video_path}"}

    try:
        youtube = build("youtube", "v3", credentials=creds)

        body = {
            "snippet": {
                "title": title[:100],   # YouTube 100-char limit
                "description": description[:5000],
                "tags": (tags or [])[:500],
                "categoryId": category_id,
                "defaultLanguage": "en",
            },
            "status": {
                "privacyStatus": privacy_status,
                "selfDeclaredMadeForKids": False,
                "notifySubscribers": notify_subscribers,
            }
        }

        media = MediaFileUpload(
            video_path,
            mimetype="video/mp4",
            resumable=True,
            chunksize=5 * 1024 * 1024,  # 5 MB chunks
        )

        request = youtube.videos().insert(
            part=",".join(body.keys()),
            body=body,
            media_body=media,
        )

        response = None
        print(f"[YouTube] Uploading: {title}")
        while response is None:
            status, response = request.next_chunk()
            if status:
                pct = int(status.progress() * 100)
                print(f"[YouTube] Upload progress: {pct}%")

        video_id = response["id"]
        url = f"https://www.youtube.com/watch?v={video_id}"
        print(f"[YouTube] Upload complete: {url}")

        # Set thumbnail if provided
        if thumbnail_path and Path(thumbnail_path).exists():
            try:
                youtube.thumbnails().set(
                    videoId=video_id,
                    media_body=MediaFileUpload(thumbnail_path, mimetype="image/png"),
                ).execute()
                print(f"[YouTube] Thumbnail set.")
            except Exception as te:
                print(f"[YouTube] Thumbnail upload failed (non-fatal): {te}")

        # Add to playlist if provided
        if playlist_id:
            try:
                youtube.playlistItems().insert(
                    part="snippet",
                    body={
                        "snippet": {
                            "playlistId": playlist_id,
                            "resourceId": {"kind": "youtube#video", "videoId": video_id}
                        }
                    }
                ).execute()
                print(f"[YouTube] Added to playlist {playlist_id}")
            except Exception as pe:
                print(f"[YouTube] Playlist add failed (non-fatal): {pe}")

        return {"status": "success", "video_id": video_id, "url": url}

    except Exception as e:
        return {"status": "error", "reason": str(e)}


# ─────────────────────────────────────────────────────────────────────────────
# CHANNEL INFO
# ─────────────────────────────────────────────────────────────────────────────

def get_channel_info() -> Optional[Dict]:
    """Return basic info about the authenticated YouTube channel."""
    from googleapiclient.discovery import build

    creds = get_credentials()
    if not creds:
        return None
    try:
        youtube = build("youtube", "v3", credentials=creds)
        resp = youtube.channels().list(part="snippet,statistics", mine=True).execute()
        items = resp.get("items", [])
        if not items:
            return None
        ch = items[0]
        return {
            "title":       ch["snippet"]["title"],
            "description": ch["snippet"].get("description", ""),
            "subscribers": ch["statistics"].get("subscriberCount", "?"),
            "total_views": ch["statistics"].get("viewCount", "?"),
            "video_count": ch["statistics"].get("videoCount", "?"),
            "channel_id":  ch["id"],
            "url": f"https://www.youtube.com/channel/{ch['id']}",
        }
    except Exception:
        return None


def list_recent_uploads(max_results: int = 10) -> list:
    """Return a list of recently uploaded videos."""
    from googleapiclient.discovery import build

    creds = get_credentials()
    if not creds:
        return []
    try:
        youtube = build("youtube", "v3", credentials=creds)
        resp = youtube.search().list(
            part="snippet",
            forMine=True,
            type="video",
            order="date",
            maxResults=max_results,
        ).execute()
        videos = []
        for item in resp.get("items", []):
            videos.append({
                "video_id": item["id"]["videoId"],
                "title": item["snippet"]["title"],
                "published": item["snippet"]["publishedAt"],
                "url": f"https://www.youtube.com/watch?v={item['id']['videoId']}",
                "thumbnail": item["snippet"]["thumbnails"].get("medium", {}).get("url", ""),
            })
        return videos
    except Exception:
        return []
