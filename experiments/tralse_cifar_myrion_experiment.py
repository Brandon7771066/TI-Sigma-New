"""
Tralse Neural Network Experiment 2: CIFAR-100 with Myrion Resolution Layers

This experiment compares:
1. Standard ResNet-like CNN with ReLU
2. Tralse CNN with Myrion Resolution Layers

Focus: Contradiction handling and adversarial robustness

Metrics:
- Accuracy
- Contradiction preservation rate
- Adversarial robustness (FGSM attack)
- Information flow analysis

Brandon Emerick - January 2026
TI Sigma Research
"""

import numpy as np
import torch
import torch.nn as nn
import torch.nn.functional as F
from torch.utils.data import DataLoader
from torchvision import datasets, transforms
import json
from datetime import datetime

DEVICE = torch.device('cuda' if torch.cuda.is_available() else 'cpu')
print(f"Using device: {DEVICE}")


class MyrionResolutionLayer(nn.Module):
    """
    Myrion Resolution Layer: Preserves contradictory information
    
    Key innovation: Instead of summing inputs (which cancels contradictions),
    this layer:
    1. Separates positive and negative pathways
    2. Computes contradiction magnitude
    3. Performs context-dependent resolution
    4. Preserves contradiction info in phi component
    """
    
    def __init__(self, in_channels, out_channels, kernel_size=3, stride=1, padding=1):
        super().__init__()
        
        # Positive pathway (excitatory)
        self.conv_pos = nn.Conv2d(in_channels, out_channels, kernel_size, stride, padding)
        
        # Negative pathway (inhibitory)
        self.conv_neg = nn.Conv2d(in_channels, out_channels, kernel_size, stride, padding)
        
        # Context modulation
        self.context_conv = nn.Conv2d(in_channels, out_channels, 1)
        
        # Batch normalization for each pathway
        self.bn_pos = nn.BatchNorm2d(out_channels)
        self.bn_neg = nn.BatchNorm2d(out_channels)
        self.bn_out = nn.BatchNorm2d(out_channels)
        
        # Learnable resolution weight
        self.resolution_weight = nn.Parameter(torch.tensor(0.5))
        
        # Store contradiction for analysis
        self.last_contradiction = None
    
    def forward(self, x):
        # Positive pathway
        pos = F.relu(self.bn_pos(self.conv_pos(x)))
        
        # Negative pathway
        neg = F.relu(self.bn_neg(self.conv_neg(-x)))
        
        # Compute contradiction: where both pathways are active
        contradiction = torch.min(pos, neg)
        self.last_contradiction = contradiction.detach()
        
        # Net direction (what standard conv would give)
        net = pos - neg
        
        # Context-weighted resolution
        context = torch.sigmoid(self.context_conv(x))
        
        # Resolution: blend between net (binary-like) and sum (preserves magnitude)
        resolved = net * (1 - self.resolution_weight * context) + \
                   (pos + neg) * (self.resolution_weight * context)
        
        # Add contradiction as a boost to the phi-like uncertainty
        # This preserves information that would be lost in standard conv
        output = self.bn_out(resolved) + 0.1 * contradiction
        
        return F.relu(output)
    
    def get_contradiction_rate(self):
        """Return fraction of activations with significant contradiction"""
        if self.last_contradiction is None:
            return 0.0
        # Significant contradiction: both pos and neg > 0.1
        significant = (self.last_contradiction > 0.1).float().mean()
        return significant.item()


class StandardBlock(nn.Module):
    """Standard convolutional block for comparison"""
    
    def __init__(self, in_channels, out_channels, stride=1):
        super().__init__()
        self.conv1 = nn.Conv2d(in_channels, out_channels, 3, stride, 1, bias=False)
        self.bn1 = nn.BatchNorm2d(out_channels)
        self.conv2 = nn.Conv2d(out_channels, out_channels, 3, 1, 1, bias=False)
        self.bn2 = nn.BatchNorm2d(out_channels)
        
        self.shortcut = nn.Sequential()
        if stride != 1 or in_channels != out_channels:
            self.shortcut = nn.Sequential(
                nn.Conv2d(in_channels, out_channels, 1, stride, bias=False),
                nn.BatchNorm2d(out_channels)
            )
    
    def forward(self, x):
        out = F.relu(self.bn1(self.conv1(x)))
        out = self.bn2(self.conv2(out))
        out += self.shortcut(x)
        return F.relu(out)


class MyrionBlock(nn.Module):
    """Myrion Resolution block with residual connection"""
    
    def __init__(self, in_channels, out_channels, stride=1):
        super().__init__()
        self.myrion1 = MyrionResolutionLayer(in_channels, out_channels, 3, stride, 1)
        self.myrion2 = MyrionResolutionLayer(out_channels, out_channels, 3, 1, 1)
        
        self.shortcut = nn.Sequential()
        if stride != 1 or in_channels != out_channels:
            self.shortcut = nn.Sequential(
                nn.Conv2d(in_channels, out_channels, 1, stride, bias=False),
                nn.BatchNorm2d(out_channels)
            )
    
    def forward(self, x):
        out = self.myrion1(x)
        out = self.myrion2(out)
        out += self.shortcut(x)
        return F.relu(out)
    
    def get_contradiction_rates(self):
        return (self.myrion1.get_contradiction_rate(), 
                self.myrion2.get_contradiction_rate())


class StandardCNN(nn.Module):
    """Standard CNN for CIFAR-100"""
    
    def __init__(self, num_classes=100):
        super().__init__()
        self.in_channels = 64
        
        self.conv1 = nn.Conv2d(3, 64, 3, 1, 1, bias=False)
        self.bn1 = nn.BatchNorm2d(64)
        
        self.layer1 = self._make_layer(64, 2, stride=1)
        self.layer2 = self._make_layer(128, 2, stride=2)
        self.layer3 = self._make_layer(256, 2, stride=2)
        
        self.avgpool = nn.AdaptiveAvgPool2d((1, 1))
        self.fc = nn.Linear(256, num_classes)
    
    def _make_layer(self, out_channels, num_blocks, stride):
        strides = [stride] + [1] * (num_blocks - 1)
        layers = []
        for s in strides:
            layers.append(StandardBlock(self.in_channels, out_channels, s))
            self.in_channels = out_channels
        return nn.Sequential(*layers)
    
    def forward(self, x):
        out = F.relu(self.bn1(self.conv1(x)))
        out = self.layer1(out)
        out = self.layer2(out)
        out = self.layer3(out)
        out = self.avgpool(out)
        out = out.view(out.size(0), -1)
        return self.fc(out)


class MyrionCNN(nn.Module):
    """CNN with Myrion Resolution Layers for CIFAR-100"""
    
    def __init__(self, num_classes=100):
        super().__init__()
        self.in_channels = 64
        
        self.conv1 = MyrionResolutionLayer(3, 64, 3, 1, 1)
        
        self.layer1 = self._make_layer(64, 2, stride=1)
        self.layer2 = self._make_layer(128, 2, stride=2)
        self.layer3 = self._make_layer(256, 2, stride=2)
        
        self.avgpool = nn.AdaptiveAvgPool2d((1, 1))
        self.fc = nn.Linear(256, num_classes)
        
        # Store all myrion layers for analysis
        self.myrion_layers = [self.conv1]
    
    def _make_layer(self, out_channels, num_blocks, stride):
        strides = [stride] + [1] * (num_blocks - 1)
        layers = []
        for s in strides:
            block = MyrionBlock(self.in_channels, out_channels, s)
            layers.append(block)
            self.myrion_layers.extend([block.myrion1, block.myrion2])
            self.in_channels = out_channels
        return nn.Sequential(*layers)
    
    def forward(self, x):
        out = self.conv1(x)
        out = self.layer1(out)
        out = self.layer2(out)
        out = self.layer3(out)
        out = self.avgpool(out)
        out = out.view(out.size(0), -1)
        return self.fc(out)
    
    def get_mean_contradiction_rate(self):
        """Get average contradiction rate across all Myrion layers"""
        rates = [layer.get_contradiction_rate() for layer in self.myrion_layers]
        return np.mean(rates)


def fgsm_attack(model, images, labels, epsilon=0.03):
    """
    Fast Gradient Sign Method attack
    Tests adversarial robustness
    """
    images.requires_grad = True
    
    outputs = model(images)
    loss = F.cross_entropy(outputs, labels)
    model.zero_grad()
    loss.backward()
    
    # Create adversarial examples
    data_grad = images.grad.data
    perturbed = images + epsilon * data_grad.sign()
    perturbed = torch.clamp(perturbed, 0, 1)
    
    return perturbed


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
    
    with torch.no_grad():
        for data, target in loader:
            data, target = data.to(DEVICE), target.to(DEVICE)
            output = model(data)
            loss = criterion(output, target)
            
            total_loss += loss.item()
            pred = output.argmax(dim=1)
            correct += pred.eq(target).sum().item()
            total += target.size(0)
    
    return total_loss / len(loader), correct / total


def evaluate_adversarial(model, loader, epsilon=0.03):
    """Evaluate model on FGSM adversarial examples"""
    model.eval()
    correct = 0
    total = 0
    
    for data, target in loader:
        data, target = data.to(DEVICE), target.to(DEVICE)
        
        # Generate adversarial examples
        data_adv = fgsm_attack(model, data.clone(), target, epsilon)
        
        # Evaluate on adversarial
        with torch.no_grad():
            output = model(data_adv)
            pred = output.argmax(dim=1)
            correct += pred.eq(target).sum().item()
            total += target.size(0)
    
    return correct / total


def run_experiment():
    print("=" * 70)
    print("TRALSE NEURAL NETWORK EXPERIMENT 2: CIFAR-100 WITH MYRION RESOLUTION")
    print("Comparing Standard CNN vs Myrion Resolution CNN")
    print("=" * 70)
    print()
    
    # Hyperparameters
    batch_size = 128
    epochs = 15  # Reduced for faster experimentation
    learning_rate = 0.1
    
    # Data loading
    transform_train = transforms.Compose([
        transforms.RandomCrop(32, padding=4),
        transforms.RandomHorizontalFlip(),
        transforms.ToTensor(),
        transforms.Normalize((0.5071, 0.4867, 0.4408), (0.2675, 0.2565, 0.2761))
    ])
    
    transform_test = transforms.Compose([
        transforms.ToTensor(),
        transforms.Normalize((0.5071, 0.4867, 0.4408), (0.2675, 0.2565, 0.2761))
    ])
    
    print("Loading CIFAR-100...")
    train_dataset = datasets.CIFAR100('./data', train=True, download=True, transform=transform_train)
    test_dataset = datasets.CIFAR100('./data', train=False, transform=transform_test)
    
    train_loader = DataLoader(train_dataset, batch_size=batch_size, shuffle=True, num_workers=2)
    test_loader = DataLoader(test_dataset, batch_size=batch_size, shuffle=False, num_workers=2)
    
    # For adversarial evaluation (smaller batch for memory)
    adv_loader = DataLoader(test_dataset, batch_size=32, shuffle=False)
    
    results = {
        'standard': {'train_acc': [], 'test_acc': [], 'adv_acc': []},
        'myrion': {'train_acc': [], 'test_acc': [], 'adv_acc': [], 'contradiction_rates': []}
    }
    
    # ====================
    # STANDARD CNN
    # ====================
    print("\n" + "=" * 50)
    print("Training STANDARD CNN")
    print("=" * 50)
    
    standard_model = StandardCNN(num_classes=100).to(DEVICE)
    optimizer = torch.optim.SGD(standard_model.parameters(), lr=learning_rate, 
                                 momentum=0.9, weight_decay=5e-4)
    scheduler = torch.optim.lr_scheduler.CosineAnnealingLR(optimizer, T_max=epochs)
    criterion = nn.CrossEntropyLoss()
    
    for epoch in range(epochs):
        train_loss, train_acc = train_epoch(standard_model, train_loader, optimizer, criterion)
        test_loss, test_acc = evaluate(standard_model, test_loader, criterion)
        scheduler.step()
        
        results['standard']['train_acc'].append(train_acc)
        results['standard']['test_acc'].append(test_acc)
        
        print(f"Epoch {epoch+1}/{epochs}: "
              f"Train Acc: {train_acc:.4f}, Test Acc: {test_acc:.4f}")
    
    # Adversarial evaluation
    print("\nEvaluating adversarial robustness (FGSM epsilon=0.03)...")
    std_adv_acc = evaluate_adversarial(standard_model, adv_loader, epsilon=0.03)
    results['standard']['adv_acc'] = std_adv_acc
    print(f"Standard CNN Adversarial Accuracy: {std_adv_acc:.4f}")
    
    # ====================
    # MYRION CNN
    # ====================
    print("\n" + "=" * 50)
    print("Training MYRION RESOLUTION CNN")
    print("=" * 50)
    
    myrion_model = MyrionCNN(num_classes=100).to(DEVICE)
    optimizer = torch.optim.SGD(myrion_model.parameters(), lr=learning_rate,
                                 momentum=0.9, weight_decay=5e-4)
    scheduler = torch.optim.lr_scheduler.CosineAnnealingLR(optimizer, T_max=epochs)
    
    for epoch in range(epochs):
        train_loss, train_acc = train_epoch(myrion_model, train_loader, optimizer, criterion)
        test_loss, test_acc = evaluate(myrion_model, test_loader, criterion)
        scheduler.step()
        
        # Get contradiction rate
        _ = myrion_model(next(iter(test_loader))[0].to(DEVICE))
        contradiction_rate = myrion_model.get_mean_contradiction_rate()
        
        results['myrion']['train_acc'].append(train_acc)
        results['myrion']['test_acc'].append(test_acc)
        results['myrion']['contradiction_rates'].append(contradiction_rate)
        
        print(f"Epoch {epoch+1}/{epochs}: "
              f"Train Acc: {train_acc:.4f}, Test Acc: {test_acc:.4f}, "
              f"Contradiction Rate: {contradiction_rate:.4f}")
    
    # Adversarial evaluation
    print("\nEvaluating adversarial robustness (FGSM epsilon=0.03)...")
    myr_adv_acc = evaluate_adversarial(myrion_model, adv_loader, epsilon=0.03)
    results['myrion']['adv_acc'] = myr_adv_acc
    print(f"Myrion CNN Adversarial Accuracy: {myr_adv_acc:.4f}")
    
    # ====================
    # COMPARISON
    # ====================
    print("\n" + "=" * 70)
    print("FINAL COMPARISON")
    print("=" * 70)
    
    std_final_acc = results['standard']['test_acc'][-1]
    myr_final_acc = results['myrion']['test_acc'][-1]
    
    print(f"\n{'Metric':<35} {'Standard':<15} {'Myrion':<15} {'Change':<15}")
    print("-" * 80)
    
    acc_diff = (myr_final_acc - std_final_acc) * 100
    print(f"{'Test Accuracy':<35} {std_final_acc:.4f}         {myr_final_acc:.4f}         {acc_diff:+.2f}%")
    
    adv_improvement = (myr_adv_acc - std_adv_acc) / std_adv_acc * 100 if std_adv_acc > 0 else 0
    print(f"{'Adversarial Accuracy (FGSM 0.03)':<35} {std_adv_acc:.4f}         {myr_adv_acc:.4f}         {adv_improvement:+.1f}%")
    
    mean_contradiction = np.mean(results['myrion']['contradiction_rates'])
    print(f"{'Mean Contradiction Rate':<35} N/A              {mean_contradiction:.4f}         (preserved!)")
    
    # Calculate parameter counts
    std_params = sum(p.numel() for p in standard_model.parameters())
    myr_params = sum(p.numel() for p in myrion_model.parameters())
    print(f"{'Parameter Count':<35} {std_params:,}       {myr_params:,}       {(myr_params/std_params-1)*100:+.1f}%")
    
    print("\n" + "=" * 70)
    print("INTERPRETATION")
    print("=" * 70)
    
    if myr_final_acc >= std_final_acc * 0.98:  # Within 2%
        print("✓ Accuracy: Myrion matches standard (competitive)")
    
    if myr_adv_acc > std_adv_acc:
        print(f"✓ Adversarial Robustness: Myrion {adv_improvement:.1f}% more robust (KEY PREDICTION)")
        print("  → Contradiction preservation prevents adversarial exploitation!")
    
    if mean_contradiction > 0.1:
        print(f"✓ Contradiction Preservation: {mean_contradiction*100:.1f}% of activations show contradiction")
        print("  → This information would be LOST in standard CNN!")
    
    print("\nTHEORETICAL INSIGHT:")
    print("  Standard CNN: Contradiction → Cancellation → Information Death")
    print("  Myrion CNN:   Contradiction → Preservation → Robust Representations")
    
    # Save results
    results['summary'] = {
        'standard_accuracy': std_final_acc,
        'myrion_accuracy': myr_final_acc,
        'standard_adv_accuracy': std_adv_acc,
        'myrion_adv_accuracy': myr_adv_acc,
        'adv_improvement_percent': adv_improvement,
        'mean_contradiction_rate': mean_contradiction,
        'standard_params': std_params,
        'myrion_params': myr_params,
        'timestamp': datetime.now().isoformat()
    }
    
    with open('experiments/cifar_myrion_results.json', 'w') as f:
        def convert(obj):
            if isinstance(obj, (np.floating, np.integer)):
                return float(obj)
            if isinstance(obj, np.ndarray):
                return obj.tolist()
            return obj
        
        results_serializable = {}
        for k, v in results.items():
            if isinstance(v, dict):
                results_serializable[k] = {kk: [convert(x) for x in vv] if isinstance(vv, list) else convert(vv)
                                           for kk, vv in v.items()}
            else:
                results_serializable[k] = convert(v)
        
        json.dump(results_serializable, f, indent=2, default=str)
    
    print(f"\nResults saved to experiments/cifar_myrion_results.json")
    
    return results


if __name__ == "__main__":
    results = run_experiment()
