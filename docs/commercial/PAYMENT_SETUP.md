# Commercial Payment Setup Guide

## Overview
Truth Engine Commercial V1 uses a hosted checkout provider abstraction (`StripePaymentProvider` and `ManualPaymentProvider`). This architecture ensures raw payment card credentials never touch local code or servers.

---

## Required Provider Account
1. Create or log into a **Stripe** account at [https://dashboard.stripe.com](https://dashboard.stripe.com).
2. Enable hosted checkout and payment links in the Stripe Dashboard.

---

## Environment Variables
The payment integration expects the following environment variables:

| Variable Name | Environment | Description |
| --- | --- | --- |
| `STRIPE_API_KEY` | Development / Sandbox | Secret key starting with `sk_test_...` |
| `STRIPE_API_KEY` | Production / Live | Secret key starting with `sk_live_...` |
| `STRIPE_WEBHOOK_SECRET` | Both | Webhook signing secret starting with `whsec_...` |
| `COMMERCIAL_PAYMENT_MODE` | Both | Set to `stripe` or `manual` |

---

## Setup Instructions

### Step 1: Configure `.env`
Copy `.env.example` to `.env`:
```bash
cp .env.example .env
```

Edit `.env` and add your secret credentials:
```env
STRIPE_API_KEY=sk_test_51...
STRIPE_WEBHOOK_SECRET=whsec_...
COMMERCIAL_PAYMENT_MODE=stripe
```

> **Security Note**: Never commit `.env` to version control. `.env` is included in `.gitignore`.

---

### Step 2: Testing Sandbox / Test Mode
1. Ensure `STRIPE_API_KEY` starts with `sk_test_`.
2. Run test payment checkout verification:
   ```bash
   python -m pytest products/truth_engine_alpha/tests/test_commercial_v1.py -k test_stripe_payment
   ```
3. Test Stripe test cards (e.g. `4242 4242 4242 4242`) on the hosted checkout link.

---

### Step 3: Switching to Live Payments
1. Obtain live API key (`sk_live_...`) from Stripe Dashboard -> Developers -> API Keys.
2. Update `.env` with live keys:
   ```env
   STRIPE_API_KEY=sk_live_...
   ```
3. In `results/commercial/FIRST_DOLLAR_STATUS.md`, set:
   `PAYMENT_PROVIDER_CONNECTED = COMPLETE`

---

## Status Declaration Rule
Do **NOT** set `PAYMENT_PROVIDER_CONNECTED = COMPLETE` until real `sk_test_` or `sk_live_` credentials have been placed into `.env` and verified.
Until then, `PAYMENT_ADAPTER_READY = COMPLETE` while `PAYMENT_PROVIDER_CONNECTED = MISSING`.
