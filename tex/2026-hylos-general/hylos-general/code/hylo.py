def hylo(conquer, divide, x):
    ^\tikzmark{ta}^tag^\tikzmark{tb}^, parts = divide(x)                            # split the problem
    results = [hylo(conquer, divide, p) for p in parts]   # solve the parts
    return conquer(^\tikzmark{tc}^tag^\tikzmark{td}^, results)                      # combine
