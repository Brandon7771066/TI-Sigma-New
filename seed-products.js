/**
 * GSA Product Seeding Script
 * Creates products and prices in Stripe for the Grand Stock Algorithm
 * 
 * Run with: node seed-products.js
 */

async function getStripeClient() {
  const hostname = process.env.REPLIT_CONNECTORS_HOSTNAME;
  const xReplitToken = process.env.REPL_IDENTITY
    ? 'repl ' + process.env.REPL_IDENTITY
    : process.env.WEB_REPL_RENEWAL
      ? 'depl ' + process.env.WEB_REPL_RENEWAL
      : null;

  if (!xReplitToken) {
    throw new Error('Replit token not found');
  }

  const url = new URL(`https://${hostname}/api/v2/connection`);
  url.searchParams.set('include_secrets', 'true');
  url.searchParams.set('connector_names', 'stripe');
  url.searchParams.set('environment', 'development');

  const response = await fetch(url.toString(), {
    headers: {
      'Accept': 'application/json',
      'X_REPLIT_TOKEN': xReplitToken
    }
  });

  const data = await response.json();
  const connectionSettings = data.items?.[0];

  if (!connectionSettings?.settings?.secret) {
    throw new Error('Stripe connection not found');
  }

  const Stripe = require('stripe');
  return new Stripe(connectionSettings.settings.secret, {
    apiVersion: '2024-11-20.acacia'
  });
}

async function createProducts() {
  console.log('Connecting to Stripe...');
  const stripe = await getStripeClient();
  console.log('Connected!\n');

  // Check if products already exist
  const existingProducts = await stripe.products.search({ query: "name:'GSA'" });
  if (existingProducts.data.length > 0) {
    console.log('GSA products already exist:');
    for (const prod of existingProducts.data) {
      console.log(`  - ${prod.name} (${prod.id})`);
    }
    console.log('\nTo recreate, delete existing products first in Stripe Dashboard.');
    return;
  }

  // ==================== BASIC TIER ====================
  console.log('Creating GSA Basic...');
  const basicProduct = await stripe.products.create({
    name: 'GSA Basic',
    description: 'Daily trading signals for 1 ticker. Perfect for beginners testing the algorithm.',
    metadata: {
      tier: 'basic',
      signals_per_day: '1',
      tickers: '1',
      api_access: 'false',
      support: 'email'
    }
  });

  const basicMonthly = await stripe.prices.create({
    product: basicProduct.id,
    unit_amount: 9900, // $99.00
    currency: 'usd',
    recurring: { interval: 'month' },
    metadata: { billing: 'monthly' }
  });

  const basicYearly = await stripe.prices.create({
    product: basicProduct.id,
    unit_amount: 95000, // $950.00 (2 months free)
    currency: 'usd',
    recurring: { interval: 'year' },
    metadata: { billing: 'yearly', discount: '20%' }
  });

  console.log(`  Created: ${basicProduct.id}`);
  console.log(`  Monthly: ${basicMonthly.id} ($99/mo)`);
  console.log(`  Yearly:  ${basicYearly.id} ($950/yr)\n`);

  // ==================== PRO TIER ====================
  console.log('Creating GSA Pro...');
  const proProduct = await stripe.products.create({
    name: 'GSA Pro',
    description: 'Full access to all tickers, regime classification, and API access. For active traders.',
    metadata: {
      tier: 'pro',
      signals_per_day: 'unlimited',
      tickers: 'all',
      api_access: 'true',
      support: 'priority',
      features: 'regime_classification,slack_alerts,api_access'
    }
  });

  const proMonthly = await stripe.prices.create({
    product: proProduct.id,
    unit_amount: 49900, // $499.00
    currency: 'usd',
    recurring: { interval: 'month' },
    metadata: { billing: 'monthly' }
  });

  const proYearly = await stripe.prices.create({
    product: proProduct.id,
    unit_amount: 479000, // $4,790.00 (2 months free)
    currency: 'usd',
    recurring: { interval: 'year' },
    metadata: { billing: 'yearly', discount: '20%' }
  });

  console.log(`  Created: ${proProduct.id}`);
  console.log(`  Monthly: ${proMonthly.id} ($499/mo)`);
  console.log(`  Yearly:  ${proYearly.id} ($4,790/yr)\n`);

  // ==================== ENTERPRISE TIER ====================
  console.log('Creating GSA Enterprise...');
  const enterpriseProduct = await stripe.products.create({
    name: 'GSA Enterprise',
    description: 'White-label solution with custom integration, dedicated support, and SLA. For funds and advisors.',
    metadata: {
      tier: 'enterprise',
      signals_per_day: 'unlimited',
      tickers: 'all',
      api_access: 'true',
      support: 'dedicated',
      features: 'white_label,custom_integration,sla,dedicated_support'
    }
  });

  const enterpriseMonthly = await stripe.prices.create({
    product: enterpriseProduct.id,
    unit_amount: 200000, // $2,000.00
    currency: 'usd',
    recurring: { interval: 'month' },
    metadata: { billing: 'monthly', note: 'Starting price, custom quotes available' }
  });

  console.log(`  Created: ${enterpriseProduct.id}`);
  console.log(`  Monthly: ${enterpriseMonthly.id} ($2,000+/mo)\n`);

  // ==================== SUMMARY ====================
  console.log('=' .repeat(50));
  console.log('GSA Products Created Successfully!');
  console.log('=' .repeat(50));
  console.log('\nPrice IDs for checkout integration:');
  console.log(`  Basic Monthly:      ${basicMonthly.id}`);
  console.log(`  Basic Yearly:       ${basicYearly.id}`);
  console.log(`  Pro Monthly:        ${proMonthly.id}`);
  console.log(`  Pro Yearly:         ${proYearly.id}`);
  console.log(`  Enterprise Monthly: ${enterpriseMonthly.id}`);
  console.log('\nThese IDs are now in Stripe and will sync to your database.');
}

createProducts().catch(console.error);
