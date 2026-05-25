import ast
import time


class UltimateURMCompiler:
    def __init__(self):
        self.raw_instructions = []
        self.variables = {}
        self.next_reg = 1
        self.label_counter = 0

    def Z(self, n): self.raw_instructions.append(('Z', n))
    def S(self, n): self.raw_instructions.append(('S', n))
    def T(self, m, n): self.raw_instructions.append(('T', m, n))
    def J(self, m, n, q): self.raw_instructions.append(('J', m, n, q))

    def _get_label(self):
        self.label_counter += 1
        return f"L{self.label_counter}"

    def Label(self, name):
        self.raw_instructions.append(name)

    def _get_reg(self):
        reg = self.next_reg
        self.next_reg += 1
        return reg

    def _emit_undef(self):
        loop_self = self._get_label()
        self.Label(loop_self)
        self.J(1, 1, loop_self)

    def compile(self, expression):
        self.raw_instructions = []
        self.variables = {}
        self.label_counter = 0

        tree = ast.parse(expression, mode='eval')
        self._extract_vars(tree.body)
        self.next_reg = len(self.variables) + 1

        result_reg = self._visit(tree.body)

        if result_reg != 1:
            self.T(result_reg, 1)
            result_reg = 1

        instructions = self._resolve_labels()
        max_registers = self.next_reg - 1

        return instructions, self.variables, max_registers, result_reg

    def _extract_vars(self, node):
        if isinstance(node, ast.Name):
            if node.id not in self.variables:
                self.variables[node.id] = len(self.variables) + 1
        elif isinstance(node, ast.BinOp):
            self._extract_vars(node.left)
            self._extract_vars(node.right)

    def _resolve_labels(self):
        resolved_list = []
        labels_map = {}

        for inst in self.raw_instructions:
            if isinstance(inst, str):
                labels_map[inst] = len(resolved_list) + 1
            else:
                resolved_list.append(inst)

        final_instructions = []
        for inst in resolved_list:
            if inst[0] == 'J':
                target = inst[3]
                if isinstance(target, str):
                    target = labels_map[target]
                final_instructions.append(('J', inst[1], inst[2], target))
            else:
                final_instructions.append(inst)
        return final_instructions

    def _visit(self, node):
        if isinstance(node, ast.Name):
            return self.variables[node.id]
        elif isinstance(node, ast.Constant) and isinstance(node.value, int) and node.value >= 0:
            return self._emit_constant(node.value)
        elif isinstance(node, ast.BinOp):
            left_reg = self._visit(node.left)
            right_reg = self._visit(node.right)

            op_type = type(node.op)
            if op_type == ast.Add: return self._emit_add(left_reg, right_reg)
            elif op_type == ast.Sub: return self._emit_sub(left_reg, right_reg)
            elif op_type == ast.Mult: return self._emit_mult(left_reg, right_reg)
            elif op_type in (ast.Div, ast.FloorDiv): return self._emit_div(left_reg, right_reg)
            else: raise ValueError("Операцію не підтримано.")
        else:
            raise ValueError("Синтаксис не підтримується. Використовуйте тільки +, -, *, /.")

    def _emit_constant(self, value):
        reg = self._get_reg()
        self.Z(reg)
        for _ in range(value): self.S(reg)
        return reg

    def _emit_add(self, reg_a, reg_b):
        out, c = self._get_reg(), self._get_reg()
        L_loop, L_end = self._get_label(), self._get_label()

        self.T(reg_a, out)
        self.Z(c)
        self.Label(L_loop)
        self.J(c, reg_b, L_end)
        self.S(out)
        self.S(c)
        self.J(1, 1, L_loop)
        self.Label(L_end)
        return out

    def _emit_pred(self, reg_a):
        out, c, c_next = self._get_reg(), self._get_reg(), self._get_reg()
        L_loop, L_end = self._get_label(), self._get_label()

        self.Z(out)
        self.Z(c)
        self.J(reg_a, c, L_end)
        self.Label(L_loop)
        self.T(c, c_next)
        self.S(c_next)
        self.J(reg_a, c_next, L_end)
        self.S(c)
        self.S(out)
        self.J(1, 1, L_loop)
        self.Label(L_end)
        return out

    def _emit_sub(self, reg_a, reg_b):
        out, c = self._get_reg(), self._get_reg()
        L_loop, L_end, L_undef = self._get_label(), self._get_label(), self._get_label()

        self.T(reg_a, out)
        self.Z(c)
        self.Label(L_loop)
        self.J(c, reg_b, L_end)

        zero_reg = self._get_reg()
        self.Z(zero_reg)
        self.J(out, zero_reg, L_undef)

        pred_out = self._emit_pred(out)
        self.T(pred_out, out)
        self.S(c)
        self.J(1, 1, L_loop)

        self.Label(L_undef)
        self._emit_undef()

        self.Label(L_end)
        return out

    def _emit_mult(self, reg_a, reg_b):
        out, c = self._get_reg(), self._get_reg()
        L_loop, L_end = self._get_label(), self._get_label()

        self.Z(out)
        self.Z(c)
        self.Label(L_loop)
        self.J(c, reg_b, L_end)
        add_out = self._emit_add(out, reg_a)
        self.T(add_out, out)
        self.S(c)
        self.J(1, 1, L_loop)
        self.Label(L_end)
        return out

    def _emit_div(self, reg_a, reg_b):
        out, zero_reg = self._get_reg(), self._get_reg()
        L_loop, L_end, L_undef = self._get_label(), self._get_label(), self._get_label()

        self.Z(out)
        self.Z(zero_reg)

        self.J(reg_b, zero_reg, L_undef)

        rem = self._get_reg()
        self.T(reg_a, rem)

        self.Label(L_loop)
        self.J(rem, zero_reg, L_end)

        rem_next = self._emit_sub(rem, reg_b)
        self.T(rem_next, rem)
        self.S(out)
        self.J(1, 1, L_loop)

        self.Label(L_undef)
        self._emit_undef()

        self.Label(L_end)
        return out


def format_command(cmd):
    return f"{cmd[0]}(" + " ".join(map(str, cmd[1:])) + ")"


def run_and_visualize(instructions, initial_state, max_registers, result_reg, time_limit=3.0, max_display_rows=2000):
    registers = {i: 0 for i in range(1, max_registers + 1)}

    for k, v in initial_state.items():
        registers[k] = v

    pc = 0
    step = 0

    header_cols = ["Крок", "PC", "Команда  "] + [f"R{i}" for i in range(1, max_registers + 1)]
    header = "| " + " | ".join(header_cols) + " |"
    sep = "-" * len(header)

    print(sep)
    print(header)
    print(sep)

    start = time.time()
    truncated = False
    timed_out = False

    while 0 <= pc < len(instructions):
        if time.time() - start > time_limit:
            timed_out = True
            break

        instr = instructions[pc]
        old_pc = pc + 1
        op = instr[0]

        if op == 'Z':
            registers[instr[1]] = 0
            pc += 1
        elif op == 'S':
            registers[instr[1]] = registers.get(instr[1], 0) + 1
            pc += 1
        elif op == 'T':
            registers[instr[2]] = registers.get(instr[1], 0)
            pc += 1
        elif op == 'J':
            if registers.get(instr[1], 0) == registers.get(instr[2], 0):
                pc = instr[3] - 1
            else:
                pc += 1

        step += 1

        if step <= max_display_rows:
            cmd_str = format_command(instr)
            regs_str = " | ".join([f"{registers.get(i, 0):2}" for i in range(1, max_registers + 1)])
            print(f"| {step:4} | {old_pc:2} | {cmd_str:9} | {regs_str} |")
        elif not truncated:
            truncated = True
            print("| ...  | .. | (вивід скорочено) ...")

    print(sep)
    if timed_out:
        print(f"\nЗупинено через {time_limit:g} с. Результат ненатуральний (від'ємний, неціле або ділення на нуль) — машина зациклилась.")
        print(f"Виконано кроків до зупинки: {step}")
    else:
        print(f"\nВиконання завершено за {step} кроків.")
        print(f"Фінальний результат записано в R{result_reg}: {registers.get(result_reg, 0)}")


def main():
    compiler = UltimateURMCompiler()
    print("=== МНР-СТУДІЯ: Компілятор + Дебагер ===")

    while True:
        expression = input("\nВведіть вираз (наприклад, x - y або x / y) або 'exit': ").strip()
        if expression.lower() in ['exit', 'q']: break
        if not expression: continue

        try:
            instructions, vars_map, max_regs, res_reg = compiler.compile(expression)

            print("\n--- Згенерований код МНР ---")
            for i, cmd in enumerate(instructions):
                print(f"{i+1:02d}: {format_command(cmd)}")
            print("-" * 28)
            print(f"Всього команд: {len(instructions)}. Виділено регістрів: {max_regs}")

            initial_state = {}
            if vars_map:
                print("\nВведіть числові значення для тесту:")
                for var_name, reg_num in vars_map.items():
                    while True:
                        try:
                            val_input = input(f"  {var_name} = ")
                            val = int(val_input)
                            if val < 0:
                                print("  МНР працює лише з додатними числами або 0. Спробуй ще раз.")
                                continue
                            initial_state[reg_num] = val
                            break
                        except ValueError:
                            print("  Помилка: Введено не число! Будь ласка, введіть звичайну цифру (наприклад, 5).")

            print("\nПочинаємо виконання...")
            run_and_visualize(instructions, initial_state, max_regs, res_reg)

        except Exception as e:
            print(f"Помилка: {e}")


if __name__ == "__main__":
    main()
