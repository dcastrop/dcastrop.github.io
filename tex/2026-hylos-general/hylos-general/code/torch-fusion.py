def layer(x):
    return torch.relu(x * w + b)        # 3 element-wise kernels
fast_layer = torch.compile(layer)       # 1 fused kernel, no temporaries
