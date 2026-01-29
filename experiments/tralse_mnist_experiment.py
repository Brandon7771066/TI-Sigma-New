"""
Tralse Neural Network Experiment 1: MNIST with Tralse Activation Functions (TAF)

This experiment compares:
1. Standard MLP with ReLU activation
2. Tralse MLP with TAF activation

Metrics:
- Accuracy
- Expected Calibration Error (ECE)
- Out-of-Distribution uncertainty (using Fashion-MNIST as OOD)
- Information preservation across layers

Brandon Emerick - January 2026
TI Sigma Research
"""

import numpy as np
import torch
import torch.nn as nn
import torch.nn.functional as F
from torch.utils.data import DataLoader
from torchvision import datasets, transforms
from collections import deque
import json
from datetime import datetime

DEVICE = torch.device('cuda' if torch.cuda.is_available() else 'cpu')
print(f"Using device: {DEVICE}")


class TralseActivation(nn.Module):
    """
    Tralse Activation Function (TAF)
    
    Outputs 4 values: (t, f, phi, psi) normalized on unit 4-sphere
    - t: True amplitude (positive activation)
    - f: False amplitude (negative activation) 
    - phi: Uncertainty amplitude (high when x near zero)
    - psi: Superposition amplitude (from gradient variance)
    """
    
    def __init__(self, temperature=1.0, gradient_buffer_size=10):
        super().__init__()
        self.temperature = temperature
        self.gradient_buffer_size = gradient_buffer_size
        self.gradient_buffer = deque(maxlen=gradient_buffer_size)
        self.training_step = 0
    
    def forward(self, x):
        # True component: positive activation
        t_raw = F.relu(x)
        
        # False component: negative activation (PRESERVED, not destroyed!)
        f_raw = F.relu(-x)
        
        # Phi component: uncertainty (high when x near zero)
        phi_raw = torch.exp(-x**2 / self.temperature)
        
        # Psi component: model uncertainty from gradient variance
        if self.training and len(self.gradient_buffer) > 1:
            grad_var = torch.var(torch.stack(list(self.gradient_buffer)), dim=0)
            psi_raw = torch.tanh(grad_var.mean() * torch.ones_like(x))
        else:
            psi_raw = torch.zeros_like(x) + 0.1  # Small baseline psi
        
        # Stack into 4D output
        output = torch.stack([t_raw, f_raw, phi_raw, psi_raw], dim=-1)
        
        # Normalize to unit 4-sphere
        norm = torch.norm(output, dim=-1, keepdim=True) + 1e-8
        output = output / norm
        
        return output
    
    def update_gradient_buffer(self, grad):
        """Call this with layer gradients during training"""
        if grad is not None:
            self.gradient_buffer.append(grad.detach().clone())


class TralseLinear(nn.Module):
    """
    Linear layer that accepts 4D tralse input and produces 4D tralse output
    """
    
    def __init__(self, in_features, out_features):
        super().__init__()
        # Separate weights for each tralse component
        self.W_t = nn.Linear(in_features, out_features)
        self.W_f = nn.Linear(in_features, out_features)
        self.W_phi = nn.Linear(in_features, out_features)
        self.W_psi = nn.Linear(in_features, out_features)
        
        # Context integration weights
        self.context_weight = nn.Parameter(torch.tensor(0.5))
    
    def forward(self, x):
        """
        x: (batch, features, 4) where last dim is (t, f, phi, psi)
        """
        # Extract components
        t, f, phi, psi = x[..., 0], x[..., 1], x[..., 2], x[..., 3]
        
        # Process each component (with cross-component interaction)
        # Key insight: contradiction between t and f creates phi
        t_out = self.W_t(t)
        f_out = self.W_f(f)
        
        # Myrion Resolution: detect contradiction
        contradiction = torch.min(F.relu(t_out), F.relu(f_out))
        net = t_out - f_out
        
        # Context-weighted resolution
        resolved = net * (1 - self.context_weight) + (t_out + f_out) * self.context_weight
        
        # Phi inherits from input phi + contradiction
        phi_out = self.W_phi(phi) + contradiction
        
        # Psi propagates uncertainty
        psi_out = self.W_psi(psi)
        
        # Stack output
        output = torch.stack([resolved, -resolved, phi_out, psi_out], dim=-1)
        
        # Normalize
        norm = torch.norm(output, dim=-1, keepdim=True) + 1e-8
        output = output / norm
        
        return output


class StandardMLP(nn.Module):
    """Standard MLP with ReLU for comparison"""
    
    def __init__(self, input_size=784, hidden_size=256, num_classes=10):
        super().__init__()
        self.fc1 = nn.Linear(input_size, hidden_size)
        self.fc2 = nn.Linear(hidden_size, hidden_size)
        self.fc3 = nn.Linear(hidden_size, num_classes)
        self.dropout = nn.Dropout(0.2)
    
    def forward(self, x):
        x = x.view(x.size(0), -1)
        x = F.relu(self.fc1(x))
        self.layer1_activations = x.detach()  # Store for analysis
        x = self.dropout(x)
        x = F.relu(self.fc2(x))
        self.layer2_activations = x.detach()
        x = self.dropout(x)
        x = self.fc3(x)
        return x
    
    def get_confidence(self, logits):
        """Return max softmax probability as confidence"""
        probs = F.softmax(logits, dim=-1)
        confidence, _ = probs.max(dim=-1)
        return confidence


class TralseMLP(nn.Module):
    """MLP with Tralse Activation Functions"""
    
    def __init__(self, input_size=784, hidden_size=256, num_classes=10):
        super().__init__()
        self.input_proj = nn.Linear(input_size, hidden_size)
        self.taf1 = TralseActivation(temperature=1.0)
        self.tralse_linear1 = TralseLinear(hidden_size, hidden_size)
        self.taf2 = TralseActivation(temperature=1.0)
        self.tralse_linear2 = TralseLinear(hidden_size, hidden_size)
        
        # Output projection: combine tralse components back to logits
        self.output_proj = nn.Linear(hidden_size * 4, num_classes)
        self.dropout = nn.Dropout(0.2)
    
    def forward(self, x):
        x = x.view(x.size(0), -1)
        
        # Initial projection
        x = self.input_proj(x)
        
        # First tralse layer
        x = self.taf1(x)
        self.layer1_tralse = x.detach()  # Store for analysis
        x = self.tralse_linear1(x)
        x = self.dropout(x.view(x.size(0), -1)).view(x.shape)
        
        # Second tralse layer
        x = self.taf2(x)
        self.layer2_tralse = x.detach()
        x = self.tralse_linear2(x)
        x = self.dropout(x.view(x.size(0), -1)).view(x.shape)
        
        # Flatten tralse output and project to classes
        x = x.view(x.size(0), -1)
        logits = self.output_proj(x)
        
        return logits
    
    def get_confidence(self, logits):
        """Return confidence based on both softmax AND phi component"""
        probs = F.softmax(logits, dim=-1)
        softmax_conf, _ = probs.max(dim=-1)
        
        # Also consider phi (uncertainty) from last layer
        if hasattr(self, 'layer2_tralse'):
            phi_mean = self.layer2_tralse[..., 2].mean(dim=-1)
            # High phi = high uncertainty = lower confidence
            tralse_conf = softmax_conf * (1 - phi_mean * 0.5)
            return tralse_conf
        return softmax_conf
    
    def get_uncertainty(self):
        """Return mean phi value (uncertainty indicator)"""
        if hasattr(self, 'layer2_tralse'):
            return self.layer2_tralse[..., 2].mean().item()
        return 0.0


def calculate_ece(confidences, predictions, labels, n_bins=10):
    """Calculate Expected Calibration Error"""
    bin_boundaries = torch.linspace(0, 1, n_bins + 1)
    ece = 0.0
    
    for i in range(n_bins):
        in_bin = (confidences > bin_boundaries[i]) & (confidences <= bin_boundaries[i+1])
        prop_in_bin = in_bin.float().mean()
        
        if prop_in_bin > 0:
            avg_confidence = confidences[in_bin].mean()
            avg_accuracy = (predictions[in_bin] == labels[in_bin]).float().mean()
            ece += prop_in_bin * torch.abs(avg_accuracy - avg_confidence)
    
    return ece.item()


def measure_information_preservation(activations):
    """Estimate information content of activations via entropy proxy"""
    # Flatten and normalize
    flat = activations.view(-1).cpu().numpy()
    
    # Estimate entropy via histogram
    hist, _ = np.histogram(flat, bins=50, density=True)
    hist = hist[hist > 0]
    entropy = -np.sum(hist * np.log2(hist + 1e-10)) * (flat.max() - flat.min()) / 50
    
    return entropy


def train_epoch(model, loader, optimizer, criterion):
    model.train()
    total_loss = 0
    correct = 0
    total = 0
    
    for batch_idx, (data, target) in enumerate(loader):
        data, target = data.to(DEVICE), target.to(DEVICE)
        
        optimizer.zero_grad()
        output = model(data)
        loss = criterion(output, target)
        loss.backward()
        optimizer.step()
        
        total_loss += loss.item()
        pred = output.argmax(dim=1)
        correct += pred.eq(target).sum().item()
        total += target.size(0)
    
    return total_loss / len(loader), correct / total


def evaluate(model, loader, criterion):
    model.eval()
    total_loss = 0
    correct = 0
    total = 0
    all_confidences = []
    all_predictions = []
    all_labels = []
    
    with torch.no_grad():
        for data, target in loader:
            data, target = data.to(DEVICE), target.to(DEVICE)
            output = model(data)
            loss = criterion(output, target)
            
            total_loss += loss.item()
            pred = output.argmax(dim=1)
            correct += pred.eq(target).sum().item()
            total += target.size(0)
            
            # Collect for ECE calculation
            confidence = model.get_confidence(output)
            all_confidences.append(confidence)
            all_predictions.append(pred)
            all_labels.append(target)
    
    # Calculate ECE
    all_confidences = torch.cat(all_confidences)
    all_predictions = torch.cat(all_predictions)
    all_labels = torch.cat(all_labels)
    ece = calculate_ece(all_confidences, all_predictions, all_labels)
    
    return total_loss / len(loader), correct / total, ece


def evaluate_ood(model, ood_loader):
    """Evaluate uncertainty on out-of-distribution data (Fashion-MNIST)"""
    model.eval()
    all_confidences = []
    
    with torch.no_grad():
        for data, _ in ood_loader:
            data = data.to(DEVICE)
            output = model(data)
            confidence = model.get_confidence(output)
            all_confidences.append(confidence)
    
    all_confidences = torch.cat(all_confidences)
    
    # Good model should have LOW confidence on OOD data
    mean_conf = all_confidences.mean().item()
    std_conf = all_confidences.std().item()
    
    return mean_conf, std_conf


def run_experiment():
    print("=" * 60)
    print("TRALSE NEURAL NETWORK EXPERIMENT 1: MNIST")
    print("Comparing Standard ReLU vs Tralse Activation Functions")
    print("=" * 60)
    print()
    
    # Hyperparameters
    batch_size = 128
    epochs = 10
    learning_rate = 0.001
    hidden_size = 256
    
    # Data loading
    transform = transforms.Compose([
        transforms.ToTensor(),
        transforms.Normalize((0.1307,), (0.3081,))
    ])
    
    print("Loading datasets...")
    train_dataset = datasets.MNIST('./data', train=True, download=True, transform=transform)
    test_dataset = datasets.MNIST('./data', train=False, transform=transform)
    
    # Fashion-MNIST for OOD evaluation
    ood_transform = transforms.Compose([
        transforms.ToTensor(),
        transforms.Normalize((0.1307,), (0.3081,))  # Same normalization
    ])
    ood_dataset = datasets.FashionMNIST('./data', train=False, download=True, transform=ood_transform)
    
    train_loader = DataLoader(train_dataset, batch_size=batch_size, shuffle=True)
    test_loader = DataLoader(test_dataset, batch_size=batch_size, shuffle=False)
    ood_loader = DataLoader(ood_dataset, batch_size=batch_size, shuffle=False)
    
    # Results storage
    results = {
        'standard': {'train_acc': [], 'test_acc': [], 'ece': [], 'info_preservation': []},
        'tralse': {'train_acc': [], 'test_acc': [], 'ece': [], 'info_preservation': [], 'phi_values': []}
    }
    
    # ====================
    # STANDARD MODEL
    # ====================
    print("\n" + "=" * 40)
    print("Training STANDARD MLP (ReLU)")
    print("=" * 40)
    
    standard_model = StandardMLP(hidden_size=hidden_size).to(DEVICE)
    optimizer = torch.optim.Adam(standard_model.parameters(), lr=learning_rate)
    criterion = nn.CrossEntropyLoss()
    
    for epoch in range(epochs):
        train_loss, train_acc = train_epoch(standard_model, train_loader, optimizer, criterion)
        test_loss, test_acc, ece = evaluate(standard_model, test_loader, criterion)
        
        results['standard']['train_acc'].append(train_acc)
        results['standard']['test_acc'].append(test_acc)
        results['standard']['ece'].append(ece)
        
        # Measure information preservation
        _ = standard_model(next(iter(test_loader))[0].to(DEVICE))
        info_l1 = measure_information_preservation(standard_model.layer1_activations)
        info_l2 = measure_information_preservation(standard_model.layer2_activations)
        results['standard']['info_preservation'].append((info_l1, info_l2))
        
        print(f"Epoch {epoch+1}/{epochs}: "
              f"Train Acc: {train_acc:.4f}, Test Acc: {test_acc:.4f}, "
              f"ECE: {ece:.4f}, Info L1/L2: {info_l1:.2f}/{info_l2:.2f}")
    
    # OOD evaluation
    std_ood_conf, std_ood_std = evaluate_ood(standard_model, ood_loader)
    print(f"\nOOD (Fashion-MNIST) Confidence: {std_ood_conf:.4f} +/- {std_ood_std:.4f}")
    print("(Lower is better - model should be uncertain on OOD)")
    
    # ====================
    # TRALSE MODEL
    # ====================
    print("\n" + "=" * 40)
    print("Training TRALSE MLP (TAF)")
    print("=" * 40)
    
    tralse_model = TralseMLP(hidden_size=hidden_size).to(DEVICE)
    optimizer = torch.optim.Adam(tralse_model.parameters(), lr=learning_rate)
    
    for epoch in range(epochs):
        train_loss, train_acc = train_epoch(tralse_model, train_loader, optimizer, criterion)
        test_loss, test_acc, ece = evaluate(tralse_model, test_loader, criterion)
        
        results['tralse']['train_acc'].append(train_acc)
        results['tralse']['test_acc'].append(test_acc)
        results['tralse']['ece'].append(ece)
        
        # Measure tralse-specific metrics
        _ = tralse_model(next(iter(test_loader))[0].to(DEVICE))
        phi_value = tralse_model.get_uncertainty()
        results['tralse']['phi_values'].append(phi_value)
        
        # Information preservation for tralse (use t component)
        t_activations = tralse_model.layer1_tralse[..., 0]
        info_l1 = measure_information_preservation(t_activations)
        t_activations = tralse_model.layer2_tralse[..., 0]
        info_l2 = measure_information_preservation(t_activations)
        results['tralse']['info_preservation'].append((info_l1, info_l2))
        
        print(f"Epoch {epoch+1}/{epochs}: "
              f"Train Acc: {train_acc:.4f}, Test Acc: {test_acc:.4f}, "
              f"ECE: {ece:.4f}, Phi: {phi_value:.4f}, Info: {info_l1:.2f}/{info_l2:.2f}")
    
    # OOD evaluation
    tralse_ood_conf, tralse_ood_std = evaluate_ood(tralse_model, ood_loader)
    print(f"\nOOD (Fashion-MNIST) Confidence: {tralse_ood_conf:.4f} +/- {tralse_ood_std:.4f}")
    
    # ====================
    # COMPARISON
    # ====================
    print("\n" + "=" * 60)
    print("FINAL COMPARISON")
    print("=" * 60)
    
    std_final_acc = results['standard']['test_acc'][-1]
    tralse_final_acc = results['tralse']['test_acc'][-1]
    std_final_ece = results['standard']['ece'][-1]
    tralse_final_ece = results['tralse']['ece'][-1]
    
    print(f"\n{'Metric':<30} {'Standard':<15} {'Tralse':<15} {'Improvement':<15}")
    print("-" * 75)
    
    acc_diff = (tralse_final_acc - std_final_acc) * 100
    print(f"{'Test Accuracy':<30} {std_final_acc:.4f}         {tralse_final_acc:.4f}         {acc_diff:+.2f}%")
    
    ece_improvement = (std_final_ece - tralse_final_ece) / std_final_ece * 100 if std_final_ece > 0 else 0
    print(f"{'ECE (lower=better)':<30} {std_final_ece:.4f}         {tralse_final_ece:.4f}         {ece_improvement:+.1f}%")
    
    ood_improvement = (std_ood_conf - tralse_ood_conf) / std_ood_conf * 100 if std_ood_conf > 0 else 0
    print(f"{'OOD Confidence (lower=better)':<30} {std_ood_conf:.4f}         {tralse_ood_conf:.4f}         {ood_improvement:+.1f}%")
    
    std_info = results['standard']['info_preservation'][-1]
    tralse_info = results['tralse']['info_preservation'][-1]
    info_ratio = tralse_info[1] / std_info[1] if std_info[1] > 0 else 1
    print(f"{'Info Preservation L2':<30} {std_info[1]:.2f}           {tralse_info[1]:.2f}           {info_ratio:.2f}x")
    
    print("\n" + "=" * 60)
    print("INTERPRETATION")
    print("=" * 60)
    
    if tralse_final_acc >= std_final_acc:
        print("✓ Accuracy: Tralse matches or exceeds standard")
    else:
        print(f"  Accuracy: Standard slightly higher ({acc_diff:.2f}% difference)")
    
    if tralse_final_ece < std_final_ece:
        print(f"✓ Calibration: Tralse {ece_improvement:.1f}% better ECE (PREDICTED IMPROVEMENT)")
    
    if tralse_ood_conf < std_ood_conf:
        print(f"✓ Uncertainty: Tralse {ood_improvement:.1f}% lower OOD confidence (correctly uncertain)")
    
    if info_ratio > 1:
        print(f"✓ Information: Tralse preserves {info_ratio:.2f}x more info in deep layers")
    
    # Save results
    results['summary'] = {
        'standard_accuracy': std_final_acc,
        'tralse_accuracy': tralse_final_acc,
        'standard_ece': std_final_ece,
        'tralse_ece': tralse_final_ece,
        'standard_ood_conf': std_ood_conf,
        'tralse_ood_conf': tralse_ood_conf,
        'info_ratio': info_ratio,
        'timestamp': datetime.now().isoformat()
    }
    
    with open('experiments/mnist_tralse_results.json', 'w') as f:
        # Convert numpy/torch to python types
        def convert(obj):
            if isinstance(obj, (np.floating, np.integer)):
                return float(obj)
            if isinstance(obj, np.ndarray):
                return obj.tolist()
            if isinstance(obj, tuple):
                return list(obj)
            return obj
        
        results_serializable = {}
        for k, v in results.items():
            if isinstance(v, dict):
                results_serializable[k] = {kk: [convert(x) for x in vv] if isinstance(vv, list) else convert(vv) 
                                           for kk, vv in v.items()}
            else:
                results_serializable[k] = convert(v)
        
        json.dump(results_serializable, f, indent=2, default=str)
    
    print(f"\nResults saved to experiments/mnist_tralse_results.json")
    
    return results


if __name__ == "__main__":
    results = run_experiment()
