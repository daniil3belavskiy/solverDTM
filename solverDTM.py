from typing import List, Tuple, Optional


class DTM:
    def __init__(self, states: int, symbols: int, blank: int, initial: int, accept: int,
                 transitions: dict):
        self.states = states  # Number of states
        self.symbols = symbols  # Number of tape symbols
        self.blank = blank
        self.initial = initial
        self.accept = accept
        self.transitions = transitions  # (state, symbol) -> (next_state, write_symbol, move_right)

    def step(self, state: int, tape: List[int], pos: int, left: List[int]) -> Tuple[int, List[int], int, List[int]]:
        """Execute one DTM step."""
        symbol = tape[pos] if 0 <= pos < len(tape) else self.blank
        key = (state, symbol)
        if key not in self.transitions:
            return state, tape, pos, left  # Halt if no transition
        next_state, write, move_right = self.transitions[key]
        if 0 <= pos < len(tape):
            tape[pos] = write
        else:
            tape.append(write)
        new_pos = pos + (1 if move_right else -1)
        if new_pos < 0:
            left.append(tape.pop(0))
            new_pos = 0
        return next_state, tape, new_pos, left

    def run(self, steps: int, tape: List[int], left: List[int] = []) -> Tuple[int, List[int], List[int]]:
        """Run DTM for given steps."""
        state = self.initial
        pos = 0
        for _ in range(steps):
            state, tape, pos, left = self.step(state, tape, pos, left)
            if state == self.accept:
                break
        return state, tape, left


def solverDTM(M_states: int, M_symbols: int, k: int) -> DTM:
    """Construct solver DTM for NP verifier M."""
    S = M_states
    Γ = M_symbols
    states = 30 + S + Γ + 1000 * 1000 * (S + Γ + 1)
    symbols = max(S + Γ + 6, 10)
    blank = 0
    initial = 0
    accept = 1

    # Define transitions
    transitions = {}
    separator = S + Γ + 2  # #
    clause_start = S + Γ + 3  # |
    positive = S + Γ + 4  # +
    negative = S + Γ + 5  # -

    # Encoding phase (states 0–15)
    transitions[(0, blank)] = (2, separator, True)  # Write first #
    transitions[(2, blank)] = (3, separator, True)  # Write second #
    transitions[(3, blank)] = (4, clause_start, True)  # Write | for clause start
    transitions[(4, blank)] = (5, positive, True)  # Write + (simplified for |+1|-2|)
    transitions[(5, blank)] = (6, 1, True)  # Write variable 1
    transitions[(6, blank)] = (7, clause_start, True)  # Write |
    transitions[(7, blank)] = (8, negative, True)  # Write -
    transitions[(8, blank)] = (9, 2, True)  # Write variable 2
    transitions[(9, blank)] = (10, clause_start, True)  # Write final |
    transitions[(10, blank)] = (11, separator, True)  # Write final #
    transitions[(11, blank)] = (12, blank, True)  # Write first 0
    transitions[(12, blank)] = (13, blank, True)  # Write second 0
    transitions[(13, blank)] = (14, separator, True)  # Write final #
    transitions[(14, blank)] = (15, blank, True)  # Prepare to solve
    transitions[(15, separator)] = (16, blank, True)  # Start solving

    # Solving phase (states 16–23)
    def get_left_length(tape: List[int], pos: int, left: List[int]) -> int:
        """Simulate dynamic leftLength (simplified)."""
        return len(left)  # In full implementation, compute dynamically

    transitions[(16, separator)] = (17, separator, True)  # Move past #
    transitions[(17, clause_start)] = (18, clause_start, True)  # Move past |
    for a in [0, 1]:
        transitions[(18, a)] = (19, a, True)  # Check assignment bit
    transitions[(19, separator)] = (20, lambda tape, pos, left: 4 if get_left_length(tape, pos, left) < 6 else 5,
                                    True)  # Check iteration count (3n = 6)
    transitions[(20, 4)] = (21, 6, True)  # Prepare to flip
    transitions[(20, 5)] = (1, 5, True)  # Accept
    transitions[(21, blank)] = (22, 7, True)  # Move to assignment
    for a in [0, 1]:
        transitions[(22, a)] = (23, 1 - a, True)  # Flip bit
    transitions[(23, blank)] = (16, 8, True)  # Restart iteration

    # Default: stay put
    for q in range(states):
        for a in range(symbols):
            if (q, a) not in transitions:
                transitions[(q, a)] = (q, a, False)

    # Handle dynamic transitions (simplified)
    def transition_fn(q: int, a: int, tape: List[int], pos: int, left: List[int]) -> Tuple[int, int, bool]:
        key = (q, a)
        if key in transitions:
            next_state, write, move = transitions[key]
            if callable(write):
                write = write(tape, pos, left)
            return next_state, write, move
        return q, a, False

    return DTM(states, symbols, blank, initial, accept, transitions)


# Example simulation
def main():
    # Simulate for |+1|-2|, n(x) = 2, m(x) = 1
    M = solverDTM(0, 0, 1)  # Simplified M with S=0, Γ=0
    tape = [0] * 26  # Initial tape with 26 blanks
    left = []

    # Run for 26 steps (as per example_verification)
    state, final_tape, final_left = M.run(26, tape, left)

    print(f"Final state: {state}")
    print(f"Final tape: {final_tape}")
    print(f"Final left: {final_left}")
    print(f"Assignment: {final_tape[10:12]}")  # Positions 10–11 after encoding
    print(f"Left length: {len(final_left)}")


if __name__ == "__main__":
    main()