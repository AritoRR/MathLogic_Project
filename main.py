import dd.autoref as _bdd
import time


def solve_factories_bdd_dd():
    print("Выберите режим работы:")
    print("0 - Без склейки")
    print("1 - Со склейкой")

    mode = input("Введите 0 или 1: ").strip()
    if mode == "0":
        print("Режим: Без склейки")
        with_wrap = False
    elif mode == "1":
        print("Режим: Со склейкой")
        with_wrap = True
    else:
        print("Неверный ввод, используется режим по умолчанию: Без склейки")
        with_wrap = False

    N = 9
    M = 4
    T = 4

    COUNTRY, COMPANY, POWER, COLOR = 0, 1, 2, 3

    countries = ["Япония", "Германия", "Франция", "Китай", "Корея",
                 "Италия", "Англия", "США", "Россия"]
    companies = ["Honda", "Porsche", "Peugeot", "Geely", "Kia",
                 "Ferrari", "Jaguar", "Ford", "Lada"]
    powers = ["100", "110", "130", "170", "250", "410", "730", "850", "955"]
    colors = ["Красный", "Зеленый", "Синий", "Белый", "Черный",
              "Бежевый", "Фиолетовый", "Розовый", "Желтый"]

    property_dict = {
        "COUNTRY": COUNTRY,
        "COMPANY": COMPANY,
        "POWER": POWER,
        "COLOR": COLOR,
    }

    value_dicts = {
        COUNTRY: {name: idx for idx, name in enumerate(countries)},
        COMPANY: {name: idx for idx, name in enumerate(companies)},
        POWER: {name: idx for idx, name in enumerate(powers)},
        COLOR: {name: idx for idx, name in enumerate(colors)}
    }

    output_file = open("solutions.txt", "w", encoding="utf-8")
    output_file.write(f"Режим работы: {'Со склейкой' if with_wrap else 'Без склейки'}\n")

    bdd = _bdd.BDD()

    var_names = []
    for i in range(N):
        for k in range(M):
            for bit in range(T):
                var_name = f'x_{i}_{k}_{bit}'
                var_names.append(var_name)

    bdd.declare(*var_names)

    def var_name(factory, property, bit):
        return f'x_{factory}_{property}_{bit}'

    def encode_p(property, factory, value):
        if value < 0 or value >= N:
            return bdd.false
        expr = bdd.true
        for bit in range(T):
            var = var_name(factory, property, bit)
            if (value >> bit) & 1:
                expr = expr & bdd.var(var)
            else:
                expr = expr & ~bdd.var(var)
        return expr

    p = [[[None for _ in range(N)] for _ in range(N)] for _ in range(M)]

    for k in range(M):
        for i in range(N):
            for j in range(N):
                p[k][i][j] = encode_p(k, i, j)

    task = bdd.true

    for i in range(N):
        for k in range(M):
            exactly_one = bdd.false
            for j in range(N):
                exactly_one = exactly_one | p[k][i][j]

            mutually_exclusive = bdd.true
            for j1 in range(N):
                for j2 in range(j1 + 1, N):
                    mutually_exclusive = mutually_exclusive & ~(p[k][i][j1] & p[k][i][j2])

            task = task & exactly_one & mutually_exclusive

    if with_wrap:
        northeast_neighbors = [(3, 1), (4, 2), (5, 0), (6, 4), (7, 5), (8, 3)]
        southeast_neighbors = [(0, 4), (1, 5), (2, 3), (3, 7), (4, 8), (5, 6)]
    else:
        northeast_neighbors = [(3, 1), (4, 2), (6, 4), (7, 5)]
        southeast_neighbors = [(0, 4), (1, 5), (3, 7), (4, 8)]

    adjacent_neighbors = northeast_neighbors + southeast_neighbors

    def get_property_index(property_name):
        return property_dict[property_name.upper()]

    def get_value_index(property_name, value_name):
        property_idx = get_property_index(property_name)
        return value_dicts[property_idx][value_name]

    def add_n1_constraint(factory, property_name, value_name):
        nonlocal task
        property_idx = get_property_index(property_name)
        value_idx = get_value_index(property_name, value_name)

        task = task & p[property_idx][factory][value_idx]

        property_names = {COUNTRY: "Страна", COMPANY: "Компания", POWER: "Мощность", COLOR: "Цвет"}
        description = f"Цех {factory} - {property_names[property_idx]} {value_name}"
        print(f"   {description}")
        return description

    def add_n2_constraint(property_from_name, value_from_name, property_to_name, value_to_name):
        nonlocal task
        property_from = get_property_index(property_from_name)
        value_from = get_value_index(property_from_name, value_from_name)
        property_to = get_property_index(property_to_name)
        value_to = get_value_index(property_to_name, value_to_name)

        for i in range(N):
            task = task & bdd.apply('->', p[property_from][i][value_from], p[property_to][i][value_to])

        description = f"{value_from_name} -> {value_to_name}"
        print(f"   {description}")
        return description

    def add_n3_constraint_relative(direction, from_property_name, from_value_name, to_property_name, to_value_name):
        nonlocal task
        from_property = get_property_index(from_property_name)
        from_value = get_value_index(from_property_name, from_value_name)
        to_property = get_property_index(to_property_name)
        to_value = get_value_index(to_property_name, to_value_name)

        constraint = bdd.false

        if direction == "southeast":
            neighbors_list = southeast_neighbors
            dir_text = "юго-восточнее"
        elif direction == "northeast":
            neighbors_list = northeast_neighbors
            dir_text = "северо-восточнее"
        else:
            raise ValueError("Направление должно быть 'southeast' или 'northeast'")

        for from_, to in neighbors_list:
            constraint = constraint | (p[from_property][from_][from_value] & p[to_property][to][to_value])

        task = task & constraint

        description = f"{to_value_name} находится {dir_text} {from_value_name}"
        print(f"   {description}")
        return description

    def add_n4_constraint_neighbors(property1_name, value1_name, property2_name, value2_name):
        nonlocal task
        property1 = get_property_index(property1_name)
        value1 = get_value_index(property1_name, value1_name)
        property2 = get_property_index(property2_name)
        value2 = get_value_index(property2_name, value2_name)

        constraint = bdd.false
        for a, b in adjacent_neighbors:
            constraint = constraint | (p[property1][a][value1] & p[property2][b][value2]) | (
                    p[property1][b][value1] & p[property2][a][value2])
        task = task & constraint

        description = f"{value1_name} соседствует с {value2_name}"
        print(f"   {description}")
        return description

    print("Ограничения первого типа:")
    add_n1_constraint(0, "COUNTRY", "Япония")
    add_n1_constraint(1, "COUNTRY", "Франция")
    add_n1_constraint(4, "POWER", "250")
    add_n1_constraint(8, "COLOR", "Желтый")
    add_n1_constraint(2, "COMPANY", "Ferrari")
    add_n1_constraint(2, "COLOR", "Белый")
    add_n1_constraint(1, "POWER", "170")

    if with_wrap:
        add_n1_constraint(0, "COLOR", "Зеленый")

    print("Ограничения второго типа:")
    add_n2_constraint("COUNTRY", "Англия", "POWER", "410")
    add_n2_constraint("COUNTRY", "США", "COLOR", "Синий")
    add_n2_constraint("COUNTRY", "Корея", "COMPANY", "Kia")
    add_n2_constraint("POWER", "130", "COLOR", "Черный")
    add_n2_constraint("COMPANY", "Geely", "POWER", "100")
    add_n2_constraint("COMPANY", "Jaguar", "COLOR", "Зеленый")

    if not with_wrap:
        add_n2_constraint("COMPANY", "Peugeot", "POWER", "110")

    print("Ограничения третьего типа:")
    add_n3_constraint_relative("southeast", "COUNTRY", "Франция", "COMPANY", "Lada")
    add_n3_constraint_relative("northeast", "COMPANY", "Kia", "COLOR", "Розовый")
    add_n3_constraint_relative("northeast", "COUNTRY", "Германия", "COMPANY", "Ford")
    add_n3_constraint_relative("southeast", "COUNTRY", "Китай", "COMPANY", "Peugeot")

    if with_wrap:
        add_n3_constraint_relative("southeast", "COUNTRY", "Китай", "POWER", "410")
    else:
        add_n3_constraint_relative("southeast", "COLOR", "Красный", "POWER", "100")

    print("Ограничения четвертого типа:")
    add_n4_constraint_neighbors("COUNTRY", "Корея", "COLOR", "Бежевый")
    add_n4_constraint_neighbors("POWER", "130", "COLOR", "Фиолетовый")
    add_n4_constraint_neighbors("COUNTRY", "Китай", "COUNTRY", "Япония")
    add_n4_constraint_neighbors("COUNTRY", "Россия", "COUNTRY", "США")
    add_n4_constraint_neighbors("COLOR", "Красный", "COMPANY", "Geely")
    add_n4_constraint_neighbors("POWER", "100", "POWER", "850")

    if with_wrap:
        add_n4_constraint_neighbors("COMPANY", "Jaguar", "POWER", "850")


    print("Уникальность:")
    for k in range(4):
        property_names = ["Страна", "Компания", "Мощность", "Цвет"]
        print(f"  Свойство {property_names[k]}...")
        for j in range(N):
            for i1 in range(N):
                for i2 in range(i1 + 1, N):
                    task = task & ~(p[k][i1][j] & p[k][i2][j])

    if task == bdd.false:
        print("\nРешения не найдены! Ограничения противоречивы.")
        output_file.write("Решения не найдены! Ограничения противоречивы.\n")
        output_file.close()
        return


    def decode_solution(model, factory, property):
        value = 0
        for bit in range(T):
            var = var_name(factory, property, bit)
            if model.get(var, False):
                value |= (1 << bit)
        return value

    def get_value_name(property, value):
        if property == COUNTRY:
            return countries[value]
        elif property == COMPANY:
            return companies[value]
        elif property == POWER:
            return powers[value]
        elif property == COLOR:
            return colors[value]

    solutions = bdd.pick_iter(task, care_vars=var_names)

    valid_solutions = 0
    max_solutions = 2000

    max_country_len = max(len(country) for country in countries)
    max_company_len = max(len(company) for company in companies)
    max_power_len = max(len(power) for power in powers)
    max_color_len = max(len(color) for color in colors)

    cell_width = max_country_len + max_company_len + max_power_len + max_color_len + 3

    for model in solutions:
        valid_solutions += 1

        solution_data = []
        for i in range(N):
            country_val = decode_solution(model, i, COUNTRY)
            company_val = decode_solution(model, i, COMPANY)
            power_val = decode_solution(model, i, POWER)
            color_val = decode_solution(model, i, COLOR)

            country_name = get_value_name(COUNTRY, country_val)
            company_name = get_value_name(COMPANY, company_val)
            power_name = get_value_name(POWER, power_val)
            color_name = get_value_name(COLOR, color_val)

            solution_data.append((country_name, company_name, power_name, color_name))

        output_file.write(f"\n--- Решение {valid_solutions} ---\n")

        separator = "+" + "-" * (cell_width + 2) + "+" + "-" * (cell_width + 2) + "+" + "-" * (cell_width + 2) + "+\n"
        output_file.write(separator)

        for row in range(3):
            line = "|"
            for col in range(3):
                idx = row * 3 + col
                country, company, power, color = solution_data[idx]
                cell_content = f" {country:<{max_country_len}} {company:<{max_company_len}} {power:>{max_power_len}} {color:<{max_color_len}} "
                line += cell_content + "|"
            output_file.write(line + "\n")

            if row < 2:
                output_file.write(separator)

        output_file.write(separator)

        if valid_solutions >= max_solutions:
            break

    print(f"\nВсего найдено решений: {valid_solutions}")
    output_file.write(f"\nВсего найдено решений: {valid_solutions}\n")
    output_file.write(f"Режим работы: {'Со склейкой' if with_wrap else 'Без склейки'}\n")
    output_file.close()


if __name__ == "__main__":
    start_time = time.time()
    solve_factories_bdd_dd()
    end_time = time.time()
    print(f"\nВремя выполнения: {end_time - start_time:.2f} секунд")