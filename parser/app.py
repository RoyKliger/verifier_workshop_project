import tkinter as tk
from tkinter import ttk
import sys
import os
from typing import List, Dict

sys.path.append(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from parser.our_parser import parse_code, parse_single_annotation, boolexpr_z3ify
import verifier

def verify_code(code: str, annotations: List[str], invariants: Dict[int, str]):
  """
  Solves the verification problem for the given code and annotations.
  Args:
    code (str): The string representation of the code.
    annotations (List[str]): A list of two strings representing the annotations.
  Returns:
    None
  """
  
  parsed = parse_code(code)
  pre = boolexpr_z3ify(parse_single_annotation(annotations[0]))
  post = boolexpr_z3ify(parse_single_annotation(annotations[1]))
  verifier.solve(pre, parsed, post)

class VerifierApp:

  def __init__(self, root):
    
    self.root = root
    self.root.title('Verifier')
    self.root.resizable(0, 0)
    
    self.root.columnconfigure(0, weight=4)
    self.root.columnconfigure(1, weight=1)
    
    # put frames in columns
    self.code_input_frame, self.annotations_input_frame, self.verify_button_frame = self.create_input_frame(self.root)
    self.code_input_frame.grid(column=0, row=0)
    self.annotations_input_frame.grid(column=1, row=0)
    self.verify_button_frame.grid(column=2, row=0)

    self.entries = []
    self.entry_values = []
    self.entry_lines = []
    self.current_entry = None

  def create_input_frame(self, container):

    # code frame

    code_frame = ttk.Frame(container)

    ttk.Label(code_frame, text='Code:').grid(column=0, row=0, sticky=tk.W)
    self.code_file = tk.Text(code_frame, width=30, height=30)
    self.code_file.grid(column=0, row=1, sticky=tk.W)

    # annotations frame

    annotations_frame = ttk.Frame(container)

    ttk.Label(annotations_frame, text='Annotation1:').grid(column=0, row=0, sticky=tk.W)
    self.pre_annotation = tk.Text(annotations_frame, width=30, height=5)
    self.pre_annotation.grid(column=0, row=1, sticky=tk.W)

    ttk.Label(annotations_frame, text='Annotation2:').grid(column=0, row=2, sticky=tk.W)
    self.post_annotation = tk.Text(annotations_frame, width=30, height=5)
    self.post_annotation.grid(column=0, row=3, sticky=tk.W)

    # invariants frame
    invariants_frame = ttk.Frame(annotations_frame)
    invariants_frame.grid(column=0, row=4, sticky=tk.W)

    ttk.Label(invariants_frame, text='Loop Invariants:').grid(column=0, row=0, sticky=tk.W)
    self.annotations_button = ttk.Button(invariants_frame, text="+", command=self.add_entry, width=2)
    self.annotations_button.grid(column=1, row=0, sticky=tk.W)

    # verify button frame
    frame2 = ttk.Frame(container)
    frame2.columnconfigure(2, weight=1)
    ttk.Button(frame2, text='Verify', command=self.on_verify).grid(column=0, row=0)

    for widget in code_frame.winfo_children() + annotations_frame.winfo_children() + frame2.winfo_children():
      widget.grid(padx=5, pady=5)

    return [code_frame, annotations_frame, frame2]
  
  def add_entry(self):

    self.annotation_entries_frame = ttk.Frame(self.annotations_input_frame)
    self.annotation_entries_frame.grid(padx=0, pady=0)
    self.annotations_button.config(state='disabled')
    self.current_entry = tk.Text(self.annotation_entries_frame, width=25, height=1)
    self.current_line_entry = ttk.Combobox(self.annotation_entries_frame, values=[str(i) for i in range(20)], width=2, height=2)
    self.current_line_entry.grid(column=0, row=0, padx=0, pady=0)
    self.current_entry.grid(column=1, row=0, padx=0, pady=0)
    
    self.save_button = ttk.Button(self.annotations_input_frame, text="Add Entry", command=self.save_entry)
    self.save_button.grid()

  def save_entry(self):

    curr_line = self.current_line_entry.get()
    curr_invariant = self.current_entry.get("1.0", tk.END).strip()

    if curr_line == '' or curr_invariant == '':
      self.current_entry = None
      raise ValueError("Please fill in all fields")
    
    if self.current_entry:
      self.current_entry.config(state='disabled')
      self.entries.append(self.current_entry)
      self.entry_lines.append(curr_line)
      self.entry_values.append(curr_invariant)
      self.current_entry = None
      self.save_button.destroy()
      self.annotations_button.config(state='normal')

  def on_verify(self):
    code = self.code_file.get("1.0", tk.END)
    annotations = [self.pre_annotation.get("1.0", tk.END), self.post_annotation.get("1.0", tk.END)]
    invariants = {int(self.entry_lines[i]): self.entry_values[i] for i in range(len(self.entries))}
    verify_code(code, annotations, invariants)

def create_main_window():
  root = tk.Tk()
  app = VerifierApp(root)
  root.mainloop()

if __name__ == "__main__":
  create_main_window()
