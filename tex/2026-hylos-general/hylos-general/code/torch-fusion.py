def attn(q, k, v):
    s = torch.softmax(q @ k.transpose(-2, -1) / 8, dim=-1)
    return s @ v                    # matmul, softmax, matmul
fast = torch.compile(attn)          # rewritten: one fused attention op
