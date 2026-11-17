def f(x):
    return torch.relu(x * 2 + 1)        # 3 element-wise kernels
fast_f = torch.compile(f)               # 1 fused kernel, no temporaries
