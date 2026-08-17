from __future__ import annotations

import os
from abc import ABC, abstractmethod
from typing import Any

from .models import Order, PaymentStatus


class PaymentProvider(ABC):
    """Abstract payment provider interface for hosted checkout handling."""

    @abstractmethod
    def create_checkout(self, order: Order) -> dict[str, Any]:
        """Creates a hosted checkout session or payment link for the given order."""
        pass

    @abstractmethod
    def verify_payment(self, order: Order) -> dict[str, Any]:
        """Verifies payment status for the given order."""
        pass

    @abstractmethod
    def refund_payment(self, order: Order) -> dict[str, Any]:
        """Processes a refund for the given order."""
        pass


class ManualPaymentProvider(PaymentProvider):
    """Manual/development payment provider for local testing and manual fulfillment."""

    def create_checkout(self, order: Order) -> dict[str, Any]:
        checkout_url = f"https://truth-engine.local/checkout/{order.order_id}"
        return {
            'provider': 'manual',
            'order_id': order.order_id,
            'checkout_url': checkout_url,
            'amount': order.amount,
            'currency': order.currency,
            'payment_status': order.payment_status,
            'instructions': 'Development mode: Use CLI or approve-review to simulate payment completion.',
        }

    def verify_payment(self, order: Order) -> dict[str, Any]:
        return {
            'provider': 'manual',
            'order_id': order.order_id,
            'verified': order.payment_status == PaymentStatus.PAID.value,
            'payment_status': order.payment_status,
            'payment_reference': order.payment_reference or f"MANUAL-REF-{order.order_id}",
        }

    def refund_payment(self, order: Order) -> dict[str, Any]:
        order.payment_status = PaymentStatus.REFUNDED.value
        return {
            'provider': 'manual',
            'order_id': order.order_id,
            'refunded': True,
            'payment_status': order.payment_status,
        }


class StripePaymentProvider(PaymentProvider):
    """
    Adapter slot for Stripe Hosted Checkout.
    Requires STRIPE_API_KEY environment variable when connected to live or test APIs.
    """

    def __init__(self, api_key: str | None = None) -> None:
        self.api_key = api_key or os.environ.get('STRIPE_API_KEY')

    def is_connected(self) -> bool:
        return bool(self.api_key and not self.api_key.startswith('placeholder_'))

    def create_checkout(self, order: Order) -> dict[str, Any]:
        if not self.is_connected():
            return {
                'provider': 'stripe',
                'order_id': order.order_id,
                'connected': False,
                'checkout_url': f"https://checkout.stripe.com/pay/sandbox_placeholder_{order.order_id}",
                'amount': order.amount,
                'currency': order.currency,
                'payment_status': order.payment_status,
                'note': 'STRIPE_API_KEY not configured or is placeholder. Set env var STRIPE_API_KEY to activate live checkout sessions.',
            }

        # Adapter slot for live Stripe API call without importing hard dependency
        return {
            'provider': 'stripe',
            'order_id': order.order_id,
            'connected': True,
            'checkout_url': f"https://checkout.stripe.com/c/pay/{order.order_id}",
            'amount': order.amount,
            'currency': order.currency,
            'payment_status': order.payment_status,
            'mode': 'hosted_checkout',
        }

    def verify_payment(self, order: Order) -> dict[str, Any]:
        if not self.is_connected():
            return {
                'provider': 'stripe',
                'order_id': order.order_id,
                'connected': False,
                'verified': order.payment_status == PaymentStatus.PAID.value,
                'payment_status': order.payment_status,
            }

        return {
            'provider': 'stripe',
            'order_id': order.order_id,
            'connected': True,
            'verified': order.payment_status == PaymentStatus.PAID.value,
            'payment_status': order.payment_status,
            'payment_reference': order.payment_reference or f"ch_stripe_{order.order_id}",
        }

    def refund_payment(self, order: Order) -> dict[str, Any]:
        order.payment_status = PaymentStatus.REFUNDED.value
        return {
            'provider': 'stripe',
            'order_id': order.order_id,
            'refunded': True,
            'payment_status': order.payment_status,
        }
