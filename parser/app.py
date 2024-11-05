import tkinter as tk
from tkinter import ttk
import sys
import os
from typing import List

sys.path.append(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from parser.our_parser import parse_code, parse_single_annotation, boolexpr_z3ify
import verifier

def verify_code(code : str, annotations : List[str]):
  """
  Solves the verification problem for the given code and annotations.
    Args:
        code (str) :The string representation of the code.
        annotations (List[str]): A list of two strings representing the annotations.
    Returns:
        None
  """
  parsed = parse_code(code)
  pre = boolexpr_z3ify(parse_single_annotation(annotations[0]))
  post = boolexpr_z3ify(parse_single_annotation(annotations[1]))
  verifier.solve(pre, parsed, post)

def create_input_frame(container):
  code_frame = ttk.Frame(container)
  code_frame.columnconfigure(0, weight=1)
  code_frame.columnconfigure(1, weight=1)

  ttk.Label(code_frame, text='Code:').grid(column=0, row=0, sticky=tk.W)
  code_file = tk.Text(code_frame, width=30, height=30)
  code_file.grid(column=0, row=1, sticky=tk.W)

  annotations_frame = ttk.Frame(container)
  ttk.Label(annotations_frame, text='Annotation1:').grid(column=1, row=0, sticky=tk.W)
  annotations1_file = tk.Text(annotations_frame, width=30, height=10)
  annotations1_file.grid(column=1, row=1, sticky=tk.W)

  ttk.Label(annotations_frame, text='Annotation2:').grid(column=1, row=2, sticky=tk.W)
  annotations2_file = tk.Text(annotations_frame, width=30, height=10)
  annotations2_file.grid(column=1, row=3, sticky=tk.W)

  frame2 = ttk.Frame(container)
  frame2.columnconfigure(2, weight=1)
  ttk.Button(frame2, text='Verify', command=lambda: verify_code(
    code_file.get("1.0", tk.END), 
    [annotations1_file.get("1.0", tk.END), annotations2_file.get("1.0", tk.END)]
  )).grid(column=0, row=0)

  for widget in code_frame.winfo_children() + annotations_frame.winfo_children() + frame2.winfo_children():
    widget.grid(padx=5, pady=5)

  return [code_frame, annotations_frame, frame2]

def create_main_window():
  root = tk.Tk()
  root.title('Verifier')
  root.resizable(0, 0)

  root.columnconfigure(0, weight=4)
  root.columnconfigure(1, weight=1)

  code_input_frame, annotations_input_frame, verify_frame = create_input_frame(root)
  code_input_frame.grid(column=0, row=0)
  annotations_input_frame.grid(column=1, row=0)
  verify_frame.grid(column=2, row=0)

  root.mainloop()

if __name__ == "__main__":
  create_main_window()
