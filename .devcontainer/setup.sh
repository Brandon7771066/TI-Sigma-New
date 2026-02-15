#!/bin/bash
set -e

echo "=========================================="
echo "TI Framework - Codespaces Setup"
echo "=========================================="

echo "Installing system dependencies for weasyprint/PDF generation..."
sudo apt-get update -qq && sudo apt-get install -y -qq \
    libcairo2 libpango-1.0-0 libgdk-pixbuf2.0-0 libffi-dev \
    libpangocairo-1.0-0 2>/dev/null || true

echo "Installing Python dependencies..."
pip install --upgrade pip
pip install -r requirements-codespaces.txt

echo ""
echo "=========================================="
echo "Setup complete!"
echo "=========================================="
echo ""
echo "To run the app:"
echo "  streamlit run app.py --server.port 5000"
echo ""
echo "To run with the full gateway (API + Streamlit):"
echo "  python async_gateway.py"
echo ""
echo "Required secrets (set as Codespaces secrets):"
echo "  ALPHA_VANTAGE_API_KEY"
echo "  APCA_API_KEY_ID"
echo "  APCA_API_SECRET_KEY"
echo "  COLLECTIVE2_API_KEY"
echo "  COLLECTIVE2_SYSTEM_ID"
echo "  DATABASE_URL"
echo "  MAGAI_PASSWORD"
echo "  MAGAI_USERNAME"
echo "  PERPLEXITY_API_KEY"
echo "  PULSOID_TOKEN"
echo "  OPENAI_API_KEY"
echo "  ANTHROPIC_API_KEY"
echo ""
echo "See replit.md for full project documentation."
echo "=========================================="
