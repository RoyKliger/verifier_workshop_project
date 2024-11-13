
log_file = "log.txt"

def log(*messages):
    with open(log_file, "a") as f:
        f.write(" ".join(map(str, messages)) + "\n")
        
def clear_logs():
    with open(log_file, "w") as f:
        pass