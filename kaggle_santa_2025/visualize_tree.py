"""
Visualize the Christmas tree shape and interlocking possibilities.
Run: python visualize_tree.py
Outputs: tree_visualization.html (open in browser)
"""

import plotly.graph_objects as go
from plotly.subplots import make_subplots
import numpy as np
import math

TREE_VERTICES = [
    (0.0, 0.8),
    (0.125, 0.5),
    (0.0625, 0.5),
    (0.2, 0.25),
    (0.1, 0.25),
    (0.35, 0.0),
    (0.075, 0.0),
    (0.075, -0.2),
    (-0.075, -0.2),
    (-0.075, 0.0),
    (-0.35, 0.0),
    (-0.1, 0.25),
    (-0.2, 0.25),
    (-0.0625, 0.5),
    (-0.125, 0.5),
    (0.0, 0.8),
]

def rotate_point(x, y, angle_deg, cx=0, cy=0):
    """Rotate point around center."""
    angle_rad = math.radians(angle_deg)
    dx = x - cx
    dy = y - cy
    new_x = cx + dx * math.cos(angle_rad) - dy * math.sin(angle_rad)
    new_y = cy + dx * math.sin(angle_rad) + dy * math.cos(angle_rad)
    return new_x, new_y

def translate_points(points, dx, dy):
    """Translate points."""
    return [(x + dx, y + dy) for x, y in points]

def rotate_tree(vertices, angle_deg, cx=0, cy=0):
    """Rotate entire tree."""
    return [rotate_point(x, y, angle_deg, cx, cy) for x, y in vertices]

def create_tree_trace(vertices, color='green', name='Tree', fill=True):
    """Create Plotly trace for tree."""
    xs = [v[0] for v in vertices]
    ys = [v[1] for v in vertices]
    
    if fill:
        return go.Scatter(
            x=xs, y=ys,
            mode='lines',
            fill='toself',
            fillcolor=color,
            line=dict(color='darkgreen', width=2),
            name=name,
            opacity=0.7
        )
    else:
        return go.Scatter(
            x=xs, y=ys,
            mode='lines',
            line=dict(color=color, width=2),
            name=name
        )

def main():
    fig = make_subplots(
        rows=2, cols=2,
        subplot_titles=(
            'Single Tree Shape',
            'Tree at 0° and 180° (Head-to-Tail)',
            'Tree at 0° and 90° Attempt',
            'Multiple Trees - Phi Spiral'
        ),
        specs=[[{'type': 'scatter'}, {'type': 'scatter'}],
               [{'type': 'scatter'}, {'type': 'scatter'}]]
    )
    
    fig.add_trace(
        create_tree_trace(TREE_VERTICES, color='lightgreen', name='Tree'),
        row=1, col=1
    )
    
    minx = min(v[0] for v in TREE_VERTICES)
    maxx = max(v[0] for v in TREE_VERTICES)
    miny = min(v[1] for v in TREE_VERTICES)
    maxy = max(v[1] for v in TREE_VERTICES)
    
    fig.add_shape(
        type='rect', x0=minx, y0=miny, x1=maxx, y1=maxy,
        line=dict(color='red', dash='dash'),
        row=1, col=1
    )
    
    fig.add_annotation(
        x=0, y=1.0,
        text=f'Width: {maxx-minx:.2f}, Height: {maxy-miny:.2f}',
        showarrow=False,
        row=1, col=1
    )
    
    tree1 = translate_points(TREE_VERTICES, -0.4, 0)
    tree2 = rotate_tree(TREE_VERTICES, 180)
    tree2 = translate_points(tree2, 0.4, 0)
    
    fig.add_trace(
        create_tree_trace(tree1, color='lightgreen', name='Tree at 0°'),
        row=1, col=2
    )
    fig.add_trace(
        create_tree_trace(tree2, color='lightblue', name='Tree at 180°'),
        row=1, col=2
    )
    
    tree1 = TREE_VERTICES
    tree2 = rotate_tree(TREE_VERTICES, 90)
    tree2 = translate_points(tree2, 0.7, 0)
    
    fig.add_trace(
        create_tree_trace(tree1, color='lightgreen', name='Tree at 0°'),
        row=2, col=1
    )
    fig.add_trace(
        create_tree_trace(tree2, color='lightblue', name='Tree at 90°'),
        row=2, col=1
    )
    
    PHI = (1 + math.sqrt(5)) / 2
    colors = ['lightgreen', 'lightblue', 'lightyellow', 'lightpink', 'lightcoral']
    
    for n in range(10):
        angle = n * (360 / PHI)
        r = 0.6 * math.sqrt(n + 1)
        x = r * math.cos(math.radians(angle))
        y = r * math.sin(math.radians(angle))
        
        tree = rotate_tree(TREE_VERTICES, n * 60)
        tree = translate_points(tree, x, y)
        
        fig.add_trace(
            create_tree_trace(tree, color=colors[n % len(colors)], name=f'Tree {n}'),
            row=2, col=2
        )
    
    fig.update_layout(
        title_text='<b>Christmas Tree Shape Analysis</b><br>'
                   '<sub>THE RIDDLE: How do trees interlock to achieve 2.6x better packing?</sub>',
        showlegend=False,
        height=800,
        width=1000
    )
    
    for i in range(1, 5):
        row = (i-1) // 2 + 1
        col = (i-1) % 2 + 1
        fig.update_xaxes(scaleanchor=f'y{i}', scaleratio=1, row=row, col=col)
    
    fig.write_html('tree_visualization.html')
    print("Saved: tree_visualization.html")
    print("\nKEY OBSERVATIONS:")
    print("- Tree width: 0.70, height: 1.00")
    print("- The GAPS are between branches (tier corners)")
    print("- The PROTRUSIONS are the branch tips")
    print("- At 180° rotation, trees can nestle head-to-tail")
    print("- The optimal interlocking angle is NOT obvious!")
    print("\nTHE RIDDLE TO CRACK:")
    print("What rotation allows one tree's protrusions to fit in another's gaps?")


if __name__ == "__main__":
    main()
