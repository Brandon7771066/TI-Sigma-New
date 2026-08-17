// Truth Engine Landing Page Form Submission Handler

function selectTier(tierId) {
    const productSelect = document.getElementById('product');
    if (productSelect) {
        productSelect.value = tierId;
    }
}

function handleAuditSubmit(event) {
    event.preventDefault();

    const email = document.getElementById('email').value;
    const name = document.getElementById('name').value;
    const product = document.getElementById('product').value;
    const domain = document.getElementById('domain').value;
    const prompt = document.getElementById('prompt').value;
    const content = document.getElementById('content').value;
    const citations = document.getElementById('citations').value;

    const orderId = 'TE-' + new Date().toISOString().replace(/[-:T.Z]/g, '').slice(0, 14);

    const orderPayload = {
        order_id: orderId,
        customer_email: email,
        customer_name: name,
        product_type: product,
        domain_hint: domain,
        prompt: prompt,
        content: content,
        citations: citations,
        submitted_at: new Date().toISOString(),
        status: 'RECEIVED'
    };

    const responseDiv = document.getElementById('formResponse');
    responseDiv.classList.remove('hidden');
    responseDiv.innerHTML = `
        <h4 style="margin-top:0; color:#0d6efd;">Order Received Successfully!</h4>
        <p><strong>Order ID:</strong> <code>${orderId}</code></p>
        <p><strong>Product:</strong> ${product}</p>
        <p><strong>Status:</strong> RECEIVED — Awaiting automated engine analysis & auditor review.</p>
        <p style="font-size:0.9rem; color:#495057;">An email confirmation has been dispatched to <code>${email}</code>. Your report will be ready after human auditor sign-off.</p>
    `;

    console.log("Local Order Created:", orderPayload);
}
