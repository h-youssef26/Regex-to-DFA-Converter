import string
import time

# ---------------------------
# Step 1: Convert Regex to Postfix (Shunting Yard)
# ---------------------------
def regex_to_postfix(regex):
    precedence = {'*': 3, '+': 3, '.': 2, '|': 1}
    output, stack = '', []
    # Add explicit concatenation operator '.'
    new_regex = ''
    for i in range(len(regex)):
        new_regex += regex[i]
        if i + 1 < len(regex):
            if regex[i] not in '(|' and regex[i + 1] not in '|)*+':
                new_regex += '.'
    regex = new_regex

    for c in regex:
        if c.isalnum():
            output += c
        elif c == '(':
            stack.append(c)
        elif c == ')':
            while stack and stack[-1] != '(':
                output += stack.pop()
            stack.pop()
        else:
            while stack and stack[-1] != '(' and precedence.get(stack[-1], 0) >= precedence[c]:
                output += stack.pop()
            stack.append(c)

    while stack:
        output += stack.pop()

    return output

# ---------------------------
# Step 2: Thompson’s Construction (Regex → NFA)
# ---------------------------
class State:
    def __init__(self):
        self.edges = {}

class NFA:
    def __init__(self, start, end):
        self.start = start
        self.end = end

def postfix_to_nfa(postfix):
    stack = []
    for c in postfix:
        if c.isalnum():
            s0, s1 = State(), State()
            s0.edges[c] = [s1]
            stack.append(NFA(s0, s1))

        elif c == '.':
            nfa2, nfa1 = stack.pop(), stack.pop()
            nfa1.end.edges.setdefault('ε', []).append(nfa2.start)
            stack.append(NFA(nfa1.start, nfa2.end))

        elif c == '|':
            nfa2, nfa1 = stack.pop(), stack.pop()
            s0, s1 = State(), State()
            s0.edges['ε'] = [nfa1.start, nfa2.start]
            nfa1.end.edges.setdefault('ε', []).append(s1)
            nfa2.end.edges.setdefault('ε', []).append(s1)
            stack.append(NFA(s0, s1))

        elif c == '*':
            nfa1 = stack.pop()
            s0, s1 = State(), State()
            s0.edges.setdefault('ε', []).extend([nfa1.start, s1])
            nfa1.end.edges.setdefault('ε', []).extend([nfa1.start, s1])
            stack.append(NFA(s0, s1))

        elif c == '+':
            # One or more repetitions
            nfa1 = stack.pop()
            s0, s1 = State(), State()
            s0.edges.setdefault('ε', []).append(nfa1.start)
            nfa1.end.edges.setdefault('ε', []).extend([nfa1.start, s1])
            stack.append(NFA(s0, s1))

    return stack.pop()

# ---------------------------
# Step 3: NFA → DFA (Subset Construction)
# ---------------------------
def epsilon_closure(states):
    stack = list(states)
    closure = set(states)
    while stack:
        state = stack.pop()
        for next_state in state.edges.get('ε', []):
            if next_state not in closure:
                closure.add(next_state)
                stack.append(next_state)
    return closure

def move(states, symbol):
    result = set()
    for s in states:
        if symbol in s.edges:
            result.update(s.edges[symbol])
    return result

def nfa_to_dfa(nfa):
    symbols = set()
    to_process = [nfa.start]
    seen = set()
    while to_process:
        s = to_process.pop()
        if s not in seen:
            seen.add(s)
            for k in s.edges:
                if k != 'ε':
                    symbols.add(k)
                to_process.extend(s.edges[k])

    start = frozenset(epsilon_closure([nfa.start]))
    dfa_states = [start]
    transitions = {}
    accepting = set()
    unmarked = [start]

    while unmarked:
        state = unmarked.pop()
        for symbol in symbols:
            nxt = frozenset(epsilon_closure(move(state, symbol)))
            if nxt:
                transitions[(state, symbol)] = nxt
                if nxt not in dfa_states:
                    dfa_states.append(nxt)
                    unmarked.append(nxt)

    for state in dfa_states:
        if nfa.end in state:
            accepting.add(state)

    return dfa_states, transitions, start, accepting, symbols

# ---------------------------
# Step 4: Assign Simple Names to DFA States
# ---------------------------
def name_dfa_states(dfa_states, start, accepting):
    names = {}
    for i, state in enumerate(dfa_states):
        names[state] = f"S{i}"
    start_name = names[start]
    accepting_names = [names[s] for s in accepting]
    return names, start_name, accepting_names

# ---------------------------
# Step 5: Display DFA Table
# ---------------------------
def display_dfa(dfa_states, transitions, start, accepting, symbols):
    names, start_name, accepting_names = name_dfa_states(dfa_states, start, accepting)

    print("\nDFA Transition Table:")
    print("--------------------------------------------------------------")
    print(f"{'State':<10} | " + " | ".join(f"{sym:^10}" for sym in symbols))
    print("--------------------------------------------------------------")

    for state in dfa_states:
        row = f"{names[state]:<10} | "
        for sym in symbols:
            nxt = transitions.get((state, sym))
            row += f"{names[nxt] if nxt else '-':^10} | "
        print(row)

    print("--------------------------------------------------------------")
    print(f"Start State: {start_name}")
    print(f"Accepting State(s): {', '.join(accepting_names)}")

# ---------------------------
# Step 6: Simulate DFA
# ---------------------------
def simulate_dfa(dfa_states, transitions, start, accepting, test_str):
    current = start
    for c in test_str:
        current = transitions.get((current, c))
        if current is None:
            return False
    return current in accepting

# ---------------------------
# Step 7: Main Terminal Interface
# ---------------------------
if __name__ == "__main__":
    print(" Welcome to the Regex → DFA Converter & Simulator ")
    print("------------------------------------------------------")
    regex = input("Please enter your regular expression: ").strip()
    postfix = regex_to_postfix(regex)

    print("\n Processing your regex...")
    time.sleep(0.8)
    print(f"Regex accepted successfully!")
    print(f"Postfix form: {postfix}")

    nfa = postfix_to_nfa(postfix)
    dfa_states, transitions, start, accepting, symbols = nfa_to_dfa(nfa)

    # Display DFA transition table with readable state names
    display_dfa(dfa_states, transitions, start, accepting, symbols)

    print("\n Your DFA is ready! Now you can test any string below:")
    print("------------------------------------------------------")

    while True:
        test_str = input("\n Enter a string to test (or type 'exit' to quit): ").strip()
        if test_str.lower() == "exit":
            print("\n Thanks for using the Regex → DFA Converter! Goodbye!")
            break
        result = simulate_dfa(dfa_states, transitions, start, accepting, test_str)
        if result:
            print("Accepted!")
        else:
            print("Rejected!")
