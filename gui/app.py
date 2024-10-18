import tkinter as tk
from tkinter import TclError, ttk

def verify_code(code, annotations):

  # parse the code from the code_file tk.Text
  # parse the annotations from the annotations_file tk.Text
  # use verifier
  # return result

  # later, add notes for user?

  print(code, annotations)

  pass

def create_input_frame(container):
  frame = ttk.Frame(container)

  # grid layout for the input frame
  frame.columnconfigure(0, weight=1)
  frame.columnconfigure(1, weight=3)

  # code file
  ttk.Label(frame, text='Code:').grid(column=0, row=0, sticky=tk.W)
  code_file = tk.Text(frame, width=30, height=30)
  code_file.grid(column=0, row=1, sticky=tk.W)

  # annotations
  ttk.Label(frame, text='Annotations:').grid(column=1, row=0, sticky=tk.W)
  annotations_file = tk.Text(frame, width=30, height=30)
  annotations_file.grid(column=1, row=1, sticky=tk.W)

  frame2 = ttk.Frame(container)
  # verify button
  frame2.columnconfigure(2, weight=1)
  ttk.Button(frame2, text='Verify', command=lambda: print(code_file.get("1.0", tk.END), annotations_file.get("1.0", tk.END))).grid(column=0, row=0)
  
  for widget in frame.winfo_children() + frame2.winfo_children():
    widget.grid(padx=5, pady=5)

  return [frame,frame2]


def create_main_window():
  root = tk.Tk()
  root.title('Verifier')
  root.resizable(0, 0)
  
  # try:
  #   # windows only (remove the minimize/maximize button)
  #   root.attributes('-toolwindow', True)
  # except TclError:
  #   print('Not supported on your platform')

  # layout on the root window
  root.columnconfigure(0, weight=4)
  root.columnconfigure(1, weight=1)

  [input_frame, verify_frame] = create_input_frame(root)
  input_frame.grid(column=0, row=0)
  verify_frame.grid(column=1, row=0)

  root.mainloop()


if __name__ == "__main__":
  create_main_window()
