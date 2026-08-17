# Truth Engine Landing Page & Submission Form

## Overview
This directory contains the static landing page and customer submission interface for **Truth Engine AI Audit**.

## Deployment & Local Testing

### Local Viewing
Open `index.html` directly in any web browser, or serve via Python local HTTP server:
```bash
python -m http.server 8080 --directory products/truth_engine_alpha/web
```
Access at `http://localhost:8080`.

### Local Submission Flow
When a user submits the form on `index.html`:
1. `app.js` generates a local Order ID (`TE-YYYYMMDD...`).
2. The form submission displays an immediate confirmation with the Order ID and current audit status (`RECEIVED`).
3. To process the order locally via CLI:
   ```bash
   python -m truth_engine audit --input <submitted_content.txt> --order-id TE-000001
   python -m truth_engine approve-review --order-id TE-000001 --reviewer "Lead Auditor"
   python -m truth_engine deliver-order --order-id TE-000001
   ```

### Production Deployment Path
For static site hosting:
- Host `index.html`, `styles.css`, `app.js` on GitHub Pages, Vercel, Netlify, or AWS S3/CloudFront.
- Connect form submission to `create-order` webhook endpoint (e.g. AWS Lambda / Cloudflare Workers endpoint calling `truth_engine.commercial.create_order`).
- Integrate Stripe Checkout via `StripePaymentProvider`.
