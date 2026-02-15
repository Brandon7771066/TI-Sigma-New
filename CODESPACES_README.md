# TI Framework - GitHub Codespaces Satellite

## Quick Start

1. Open this repo in Codespaces (click "Code" > "Codespaces" > "Create codespace on main")
2. Wait for setup to complete (~3-5 minutes)
3. Run the app: `streamlit run app.py --server.port 5000`
4. Or with full API gateway: `python async_gateway.py`

## Required Secrets

Set these as **Codespaces secrets** in GitHub Settings > Codespaces > Secrets:

| Secret | Purpose |
|--------|---------|
| `OPENAI_API_KEY` | GPT-5 AI analysis |
| `ANTHROPIC_API_KEY` | Claude Opus analysis |
| `PERPLEXITY_API_KEY` | Perplexity research |
| `ALPHA_VANTAGE_API_KEY` | Stock market data |
| `APCA_API_KEY_ID` | Alpaca trading API |
| `APCA_API_SECRET_KEY` | Alpaca trading secret |
| `COLLECTIVE2_API_KEY` | Collective2 trading |
| `COLLECTIVE2_SYSTEM_ID` | Collective2 system |
| `DATABASE_URL` | PostgreSQL connection |
| `PULSOID_TOKEN` | Polar H10 heart rate |
| `MAGAI_PASSWORD` | MagAI platform |
| `MAGAI_USERNAME` | MagAI platform |

## Project Structure

- `app.py` - Main Streamlit application (multi-tab interface)
- `async_gateway.py` - Flask API gateway + Streamlit proxy (port 5000)
- `engines/` - Core computation engines
  - `focus_amplifier.py` - 7-mode ADHD focus optimization
  - `psi_tuning_protocol.py` - PSI heart coherence protocol
  - `lcc_sleep_induction.py` - LCC sleep induction protocol
- `papers/` - TI Framework academic papers
- `pages/` - Additional Streamlit pages
- `replit.md` - Complete project documentation

## Key Features

- **Focus Amplifier**: 7 biometric-driven focus modes (calm/excited concentration, open awareness, flow + active relaxation)
- **Mood Amplifier**: Real-time biometric mood optimization
- **Stock Predictor**: GSA regime classification + TI Sigma predictions
- **PSI Testing**: Heart coherence protocols for consciousness research
- **Sleep Induction**: LCC attractor basin sleep protocol

## Database

The app uses PostgreSQL. In Codespaces, you can:
- Use a cloud PostgreSQL (set `DATABASE_URL` secret)
- Or install locally: `sudo apt install postgresql && sudo service postgresql start`

## Syncing with Replit

This repo is the canonical backup. The primary development happens on Replit.
To sync changes FROM Replit: Replit pushes to this repo automatically.
To sync changes TO Replit: Push here, then pull from Replit's Git panel.
