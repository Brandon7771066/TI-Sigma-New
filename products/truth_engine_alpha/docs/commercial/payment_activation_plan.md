# Payment Activation Plan

## Platform choice
Use Stripe Payment Link (preferred) or PayPal invoice template.

## Business-facing description
Human-Reviewed AI Claim and Citation Audit (one answer, up to 20 claims).

## Refund and cancellation terms (starter)
- Full refund if work has not started.
- 50% refund if work started but delivery not completed.
- No refund after final delivery unless a documented delivery failure occurred.
- Cancellation requests must be in writing.

## Security rules
- Do not store payment credentials in repository files.
- Do not build payment processing into Truth Engine Alpha at this stage.
- Keep payment actions external to analysis pipeline.

## Ready-state checklist
- Payment link/invoice template created
- Scope and terms visible to client
- Refund/cancellation terms visible
- Internal test payment flow completed without charging real client
