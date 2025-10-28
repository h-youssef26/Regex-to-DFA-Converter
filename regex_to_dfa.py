import tkinter as tk
from tkinter import ttk, messagebox
from collections import deque
import math

# -------------------------
#  Regex -> Postfix Utilities
# -------------------------
def add_concat(regex):
    # insert '.' as explicit concatenation operator
    result = []
    operators = set('|*+?')
    prev = None
    for c in regex:
        if prev is not None:
            if (prev not in operators and prev != '(') or prev == ')' or prev in '*+?':
                if (c not in operators and c != ')') or c == '(':
                    result.append('.')
        result.append(c)
        prev = c
    return ''.join(result)

prec = {'*': 5, '+':5, '?':5, '.':4, '|':3}
def to_postfix(regex):
    regex = add_concat(regex)
    out = []
    stack = []
    for c in regex:
        if c == '(':
            stack.append(c)
        elif c == ')':
            while stack and stack[-1] != '(':
                out.append(stack.pop())
            if not stack:
                raise ValueError("Mismatched parentheses")
            stack.pop()
        elif c in prec:
            while stack and stack[-1] != '(' and prec.get(stack[-1],0) >= prec[c]:
                out.append(stack.pop())
            stack.append(c)
        else:
            out.append(c)
    while stack:
        t = stack.pop()
        if t in ('(', ')'):
            raise ValueError("Mismatched parentheses")
        out.append(t)
    return ''.join(out)

# -------------------------
# Thompson NFA construction
# -------------------------
class State:
    __slots__ = ("edges", "eps")
    def __init__(self):
        self.edges = {}  # symbol -> list of states
        self.eps = []    # list of epsilon transitions

def make_basic(sym):
    s1 = State()
    s2 = State()
    s1.edges.setdefault(sym, []).append(s2)
    return (s1, s2)

def concat(n1, n2):
    n1[1].eps.append(n2[0])
    return (n1[0], n2[1])

def union(n1, n2):
    s = State(); e = State()
    s.eps += [n1[0], n2[0]]
    n1[1].eps.append(e)
    n2[1].eps.append(e)
    return (s, e)

def kleene(n):
    s = State(); e = State()
    s.eps += [n[0], e]
    n[1].eps += [n[0], e]
    return (s, e)

def plus(n):
    # A+ = A A*
    k = kleene(n)
    return concat(n, k)

def optional(n):
    s = State(); e = State()
    s.eps += [n[0], e]
    n[1].eps.append(e)
    return (s, e)

def postfix_to_nfa(postfix):
    stack = []
    for c in postfix:
        if c == '.':
            if len(stack) < 2: raise ValueError("Invalid postfix for concatenation")
            b = stack.pop(); a = stack.pop()
            stack.append(concat(a,b))
        elif c == '|':
            if len(stack) < 2: raise ValueError("Invalid postfix for union")
            b = stack.pop(); a = stack.pop()
            stack.append(union(a,b))
        elif c == '*':
            if not stack: raise ValueError("Invalid postfix for *")
            a = stack.pop(); stack.append(kleene(a))
        elif c == '+':
            if not stack: raise ValueError("Invalid postfix for +")
            a = stack.pop(); stack.append(plus(a))
        elif c == '?':
            if not stack: raise ValueError("Invalid postfix for ?")
            a = stack.pop(); stack.append(optional(a))
        else:
            stack.append(make_basic(c))
    if len(stack) != 1:
        raise ValueError("Invalid postfix expression (stack size != 1)")
    return stack[0]

def epsilon_closure(states):
    stack = list(states)
    closure = set(states)
    while stack:
        s = stack.pop()
        for t in s.eps:
            if t not in closure:
                closure.add(t)
                stack.append(t)
    return closure

def move(states, symbol):
    result = set()
    for s in states:
        for t in s.edges.get(symbol, []):
            result.add(t)
    return result

# -------------------------
# Subset construction: NFA -> DFA
# -------------------------
def extract_alphabet(regex):
    ops = set('|*+?()')
    return sorted(list({c for c in regex if c not in ops}))

def nfa_to_dfa(nfa, alphabet):
    start = nfa[0]; accept = nfa[1]
    start_cl = frozenset(epsilon_closure([start]))
    dstates = {start_cl: 0}
    dqueue = deque([start_cl])
    transitions = {}  # id -> {symbol: id}
    state_id = 1
    # We'll use frozenset() (empty set) to represent the dead state's NFA-set
    while dqueue:
        D = dqueue.popleft()
        sid = dstates[D]
        transitions[sid] = {}
        for a in alphabet:
            m = move(D, a)
            # if m empty, we map to the explicit empty-set closure (dead)
            e = frozenset(epsilon_closure(m)) if m else frozenset()
            if e not in dstates:
                dstates[e] = state_id
                state_id += 1
                dqueue.append(e)
            transitions[sid][a] = dstates[e]
    accepting = set()
    for sset, sid in dstates.items():
        if accept in sset:
            accepting.add(sid)
    # ensure transitions exist for all states for every alphabet symbol (complete DFA) -
    # add missing entries (shouldn't be missing due to loop above but be safe)
    for sset, sid in list(dstates.items()):
        transitions.setdefault(sid, {})
        for a in alphabet:
            transitions[sid].setdefault(a, dstates.get(frozenset(), None))
    # If dead state was created, ensure it has self-loops for every symbol
    dead_id = dstates.get(frozenset(), None)
    if dead_id is not None:
        transitions.setdefault(dead_id, {})
        for a in alphabet:
            transitions[dead_id][a] = dead_id
    return {
        'start': 0,
        'transitions': transitions,
        'accepting': accepting,
        'states_map': dstates
    }

# -------------------------
# Convert DFA to numeric-friendly structure for drawing
# -------------------------
def make_dfa_from_regex(regex):
    if regex.strip() == "":
        raise ValueError("Empty regex")
    postfix = to_postfix(regex)
    nfa = postfix_to_nfa(postfix)
    alphabet = extract_alphabet(regex)
    dfa = nfa_to_dfa(nfa, alphabet)
    transitions = dfa['transitions']
    # collect all ids
    all_ids = set(transitions.keys())
    for v in transitions.values():
        all_ids.update(v.values())
    if not all_ids:
        all_ids.add(dfa['start'])
    state_count = max(all_ids) + 1
    # Build ordered transitions where every state has mapping for every alphabet symbol
    # (this is already ensured in nfa_to_dfa)
    return {
        'start': dfa['start'],
        'accepting': dfa['accepting'],
        'transitions': transitions,
        'alphabet': alphabet,
        'state_count': state_count
    }

# -------------------------
# GUI + Visualization
# -------------------------
class DFAVisualizer(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("Regex → DFA")
        self.geometry("1100x720")
        self.configure(padx=8, pady=8)
        self._create_widgets()
        self.dfa = None
        # redraw when resized for crisp layout
        self.canvas.bind("<Configure>", lambda e: self._on_resize())

    def _create_widgets(self):
        frm_top = ttk.Frame(self)
        frm_top.pack(fill="x", pady=(0,8))

        ttk.Label(frm_top, text="Enter Regex:").pack(side="left")
        self.regex_var = tk.StringVar(value="(a|b)*abb")
        self.ent_regex = ttk.Entry(frm_top, textvariable=self.regex_var, width=44)
        self.ent_regex.pack(side="left", padx=6)

        btn_convert = ttk.Button(frm_top, text="Convert", command=self.on_convert)
        btn_convert.pack(side="left", padx=(6,0))

        ttk.Label(frm_top, text=" Test string:").pack(side="left", padx=(12,0))
        self.test_var = tk.StringVar()
        self.ent_test = ttk.Entry(frm_top, textvariable=self.test_var, width=22)
        self.ent_test.pack(side="left", padx=6)
        btn_test = ttk.Button(frm_top, text="Test", command=self.on_test)
        btn_test.pack(side="left")

        # Canvas for drawing
        self.canvas = tk.Canvas(self, bg="white", highlightthickness=0)
        self.canvas.pack(fill="both", expand=True)

        # status bar
        self.status_var = tk.StringVar()
        status = ttk.Label(self, textvariable=self.status_var, anchor="w")
        status.pack(fill="x")

    def on_convert(self):
        regex = self.regex_var.get().strip()
        try:
            dfa = make_dfa_from_regex(regex)
            self.dfa = dfa
            self.status_var.set(f"Converted. States: {dfa['state_count']}, Alphabet: {dfa['alphabet']}, Accepting: {sorted(list(dfa['accepting']))}")
            messagebox.showinfo("Converted", "Regex converted to DFA. Now press Visualize to see it.")
            self.on_visualize()

        except Exception as e:
            messagebox.showerror("Error converting regex", str(e))

    def on_visualize(self):
        if not self.dfa:
            messagebox.showwarning("No DFA", "Please Convert a regex first.")
            return
        self.canvas.delete("all")
        self._draw_dfa(self.dfa)

    def on_test(self):
        if not self.dfa:
            messagebox.showwarning("No DFA", "Convert a regex first before testing strings.")
            return
        s = self.test_var.get()
        accept = self._simulate(self.dfa, s)
        if accept:
            messagebox.showinfo("Result", f"String '{s}' is ACCEPTED by the DFA.")
        else:
            messagebox.showinfo("Result", f"String '{s}' is REJECTED by the DFA.")

    def _simulate(self, dfa, string):
        cur = dfa['start']
        for ch in string:
            trans = dfa['transitions'].get(cur, {})
            if ch in trans:
                cur = trans[ch]
            else:
                return False
        return cur in dfa['accepting']

    def _on_resize(self):
        # redraw on resize for clearer layout
        if self.dfa:
            self.canvas.delete("all")
            self._draw_dfa(self.dfa)

    def _draw_arrow(self, x1, y1, x2, y2, width=2):
        # draw line and custom triangular arrowhead for clarity
        self.canvas.create_line(x1, y1, x2, y2, width=width, smooth=True)
        # arrowhead
        dx = x2 - x1
        dy = y2 - y1
        ang = math.atan2(dy, dx)
        size = 10
        p1x = x2 - size * math.cos(ang) + size/2 * math.sin(ang)
        p1y = y2 - size * math.sin(ang) - size/2 * math.cos(ang)
        p2x = x2 - size * math.cos(ang) - size/2 * math.sin(ang)
        p2y = y2 - size * math.sin(ang) + size/2 * math.cos(ang)
        self.canvas.create_polygon(x2, y2, p1x, p1y, p2x, p2y, fill="black")

    def _draw_dfa(self, dfa):
        # fetch sizes
        w = max(self.canvas.winfo_width(), 600)
        h = max(self.canvas.winfo_height(), 400)
        n = dfa['state_count']
        alphabet = dfa['alphabet']
        transitions = dfa['transitions']
        accepting = dfa['accepting']
        start = dfa['start']
        self.canvas.configure(scrollregion=(0,0,w,h))
        # background grid lightly for spatial clarity
        grid_gap = 40
        for gx in range(0, w, grid_gap):
            self.canvas.create_line(gx, 0, gx, h, fill="#f6f6f6")
        for gy in range(0, h, grid_gap):
            self.canvas.create_line(0, gy, w, gy, fill="#f6f6f6")

        # determine positions: if many states, use larger circle radius; keep nodes spaced nicely
        cx, cy = w//2, h//2
        outer_radius = min(w, h)//2 - 120
        if n <= 6:
            outer_radius = min(w, h)//2 - 70
        positions = {}
        # Put dead state at bottom-right corner if it exists for consistent location
        dead_id = None
        for sid in range(n):
            # guess dead state id by checking whether all outgoing go to itself (heuristic)
            out = transitions.get(sid, {})
            if out and all(out.get(a, None) == sid for a in alphabet):
                # only accept dead state if not accepting
                if sid not in accepting:
                    dead_id = sid
                    break
        # Place states on circle except dead (will place specially)
        idx = 0
        for i in range(n):
            if i == dead_id:
                continue
            angle = 2*math.pi * idx / max(1, n - (1 if dead_id is not None else 0))
            x = cx + int(outer_radius * math.cos(angle))
            y = cy + int(outer_radius * math.sin(angle))
            positions[i] = (x, y)
            idx += 1
        if dead_id is not None:
            positions[dead_id] = (cx + outer_radius + 80, cy + outer_radius - 80)
        # node radius scaled by canvas size, bigger for small counts
        node_r = max(20, min(48, int(min(w, h) / (n+4))))
        # collect edge labels
        edge_labels = {}
        for u, trans in transitions.items():
            for sym, v in trans.items():
                edge_labels.setdefault((u, v), []).append(sym)

        # draw edges beneath nodes
        for (u,v), syms in edge_labels.items():
            x1,y1 = positions[u]
            x2,y2 = positions[v]
            if u == v:
                # self-loop: draw arc above node
                loop_r = node_r + 18
                # position loop offset dependent on node location
                ox, oy = x1, y1 - node_r - 24
                self.canvas.create_arc(ox-loop_r, oy-loop_r, ox+loop_r, oy+loop_r, start=20, extent=300, style='arc', width=2)
                label_x = x1
                label_y = oy - loop_r - 10
                self.canvas.create_text(label_x, label_y, text=",".join(syms), font=("Arial", 11, "bold"))
            else:
                dx = x2 - x1; dy = y2 - y1
                dist = math.hypot(dx, dy)
                if dist == 0:
                    dist = 0.001
                nx = dx/dist; ny = dy/dist
                start_x = x1 + nx*node_r
                start_y = y1 + ny*node_r
                end_x = x2 - nx*node_r
                end_y = y2 - ny*node_r
                # if reverse edge exists, offset both by perpendicular to create curve separation
                if (v,u) in edge_labels and u < v:
                    px = -ny; py = nx
                    offset = node_r * 0.9
                    start_x += px*offset
                    start_y += py*offset
                    end_x += px*offset
                    end_y += py*offset
                    # draw smooth curved line (create_line with smooth True)
                    self._draw_arrow(start_x, start_y, end_x, end_y, width=2)
                elif (v,u) in edge_labels and u > v:
                    # the opposite direction will already be drawn; draw mirrored curve with negative offset
                    px = ny; py = -nx
                    offset = node_r * 0.9
                    start_x += px*offset
                    start_y += py*offset
                    end_x += px*offset
                    end_y += py*offset
                    self._draw_arrow(start_x, start_y, end_x, end_y, width=2)
                else:
                    # straight arrow
                    self._draw_arrow(start_x, start_y, end_x, end_y, width=2)
                # label slightly offset from midpoint
                mx = (start_x + end_x)/2
                my = (start_y + end_y)/2
                # perpendicular shift
                mx += -ny * (12)
                my += nx * (12)
                self.canvas.create_rectangle(mx-4, my-12, mx+4 + len(",".join(syms))*6, my+4, fill="white", outline="")
                self.canvas.create_text(mx+ (len(",".join(syms))*3)/2, my-4, text=",".join(syms), font=("Arial", 10, "bold"))

        # draw nodes on top
        for i, (x,y) in positions.items():
            r = node_r
            # dead state fill special
            if dead_id is not None and i == dead_id:
                fill = "#e9e9e9"
                outline = "#444444"
            else:
                fill = "#fffecb" if i in accepting else "#ffffff"
                outline = "#000000"
            # main circle
            self.canvas.create_oval(x-r, y-r, x+r, y+r, fill=fill, width=2, outline=outline)
            # accepting double circle
            if i in accepting:
                inner = int(r*0.7)
                self.canvas.create_oval(x-inner, y-inner, x+inner, y+inner, width=2)
            # state label
            lbl = "dead" if dead_id is not None and i == dead_id else str(i)
            # background rectangle for better contrast for label
            self.canvas.create_text(x, y, text=lbl, font=("Arial", 13, "bold"))
            # little index tag top-left
            self.canvas.create_text(x - r + 14, y - r + 12, text=f"{i}", font=("Arial", 8), fill="#333")

        # start arrow (from left)
        sx, sy = positions[start]
        # draw arrowed line from left and label
        self._draw_arrow(sx - (node_r + 60), sy, sx - node_r, sy, width=3)
        self.canvas.create_text(sx - (node_r + 85), sy, text="start", font=("Arial", 11, "italic"))

        # legend / info
        info = f"States: {dfa['state_count']}    Accepting: {sorted(list(accepting))}    Alph: {alphabet}"
        self.canvas.create_text(12, h-12, text=info, anchor="w", font=("Arial", 11, "italic"))

# -------------------------
# Run App
# -------------------------
if __name__ == "__main__":
    app = DFAVisualizer()
    app.mainloop()



