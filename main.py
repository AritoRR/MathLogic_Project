import dd.autoref as _bdd
import time


def solve_factories_bdd_dd():
    print("Starting Factory BDD Solver with dd library")

    # Константы
    N = 9  # 9 заводов
    M = 4  # 4 свойства
    T = 4  # ceil(log2(9)) = 4 бита

    # Property indices
    COUNTRY, COMPANY, POWER, COLOR = 0, 1, 2, 3

    # Значения свойств
    countries = ["Япония", "Германия", "Франция", "Китай", "Корея",
                 "Италия", "Англия", "США", "Россия"]
    companies = ["HONDA", "Porsche", "Peugeot", "Geely", "KIA",
                 "Ferrari", "Jaguar", "Ford", "Lada"]
    powers = ["100", "110", "130", "170", "250", "410", "730", "850", "955"]
    colors = ["Красный", "Зеленый", "Синий", "Белый", "Черный",
              "Бежевый", "Фиолетовый", "Розовый", "Желтый"]

    # Инициализация BDD
    bdd = _bdd.BDD()
    print(f"Creating {N * M * T} variables...")

    # Создаем переменные
    var_names = []
    for i in range(N):
        for k in range(M):
            for bit in range(T):
                var_name = f'x_{i}_{k}_{bit}'
                var_names.append(var_name)

    bdd.declare(*var_names)

    # Функция для получения имени переменной
    def var_name(factory, property, bit):
        return f'x_{factory}_{property}_{bit}'

    # Кодируем функцию p(k, i, j)
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

    # Создаем матрицу p[k][i][j]
    print("Encoding P function...")
    p = [[[None for _ in range(N)] for _ in range(N)] for _ in range(M)]

    for k in range(M):
        for i in range(N):
            for j in range(N):
                p[k][i][j] = encode_p(k, i, j)

    # Инициализируем задачу
    task = bdd.true

    # БАЗОВЫЕ ОГРАНИЧЕНИЯ: каждый завод имеет ровно одно значение для каждого свойства
    print("Adding domain constraints...")
    for i in range(N):
        for k in range(M):
            # Завод i должен иметь ровно одно значение свойства k
            exactly_one = bdd.false
            for j in range(N):
                exactly_one = exactly_one | p[k][i][j]

            # И все значения взаимоисключающие
            mutually_exclusive = bdd.true
            for j1 in range(N):
                for j2 in range(j1 + 1, N):
                    mutually_exclusive = mutually_exclusive & ~(p[k][i][j1] & p[k][i][j2])

            task = task & exactly_one & mutually_exclusive

    print("Setting up neighbors...")

    northeast_neighbors = [(3, 1), (4, 2), (5, 0), (6, 4), (7, 5), (8, 3)]
    southeast_neighbors = [(0, 4), (1, 5), (2, 3), (3, 7), (4, 8), (5, 6)]
    adjacent_neighbors = northeast_neighbors + southeast_neighbors

    # TYPE n1 Constraints - ФИКСИРОВАННЫЕ ЗНАЧЕНИЯ
    print("Adding n1 constraints (fixed values)...")
    # 1. Завод 0 (левый верхний) - Япония (0)
    task = task & p[COUNTRY][0][0]
    print("   1.Завод 0 - Япония")
    # 2. Завод 1 (середина верхней строки) - Франция (2)
    task = task & p[COUNTRY][1][2]
    print("   2.Завод 1 - Франция")
    # 3. Завод 4 (центр) - мощность 250 л.с. (4)
    task = task & p[POWER][4][4]
    print("   3.Завод 4 - мощность 250 л.с.")
    # 4. Завод 8 (правый нижний) - желтый цвет (8)
    task = task & p[COLOR][8][8]
    print("   4.Завод 8 - желтый цвет")
    # 5. Завод 2 (правый верхний) - Ferrari (5)
    task = task & p[COMPANY][2][5]
    print("   5.Завод 2 - Ferrari")
    # 6. Завод 2 (правый верхний) - белый цвет (3)
    task = task & p[COLOR][2][3]
    print("   6.Завод 2 - белый цвет")
    # 7. Завод 1 (середина верхней строки) - мощность 170 л.с. (3)
    task = task & p[POWER][1][3]
    print("   7.Завод 1 - мощность 170 л.с.")
    # 8. Завод 0 (левый верхний) - зеленый цвет (1)
    task = task & p[COLOR][0][1]
    print("   8.Завод 0 - зеленый цвет")

    # TYPE n2 Constraints - ЛОГИЧЕСКИЕ СЛЕДСТВИЯ
    print("Adding n2 constraints (logical implications)...")
    print("   1.Англия -> мощность 410 л.с.")
    print("   2.США -> синий цвет")
    print("   3.Корея -> KIA")
    print("   4.Мощность 130 л.с. -> черный цвет")
    print("   5.Geely -> мощность 100 л.с.")
    print("   6.Jaguar -> зеленый цвет")
    for i in range(N):
        # 9. Англия (6) -> мощность 410 л.с. (5)
        task = task & bdd.apply('->', p[COUNTRY][i][6], p[POWER][i][5])

        # 10. США (7) -> синий цвет (2)
        task = task & bdd.apply('->', p[COUNTRY][i][7], p[COLOR][i][2])

        # 11. Корея (4) -> KIA (4)
        task = task & bdd.apply('->', p[COUNTRY][i][4], p[COMPANY][i][4])

        # 12. Мощность 130 л.с. (2) -> черный цвет (4)
        task = task & bdd.apply('->', p[POWER][i][2], p[COLOR][i][4])

        # 13. Geely (3) -> мощность 100 л.с. (0)
        task = task & bdd.apply('->', p[COMPANY][i][3], p[POWER][i][0])

        # 14. Jaguar (6) -> зеленый цвет (1)
        task = task & bdd.apply('->', p[COMPANY][i][6], p[COLOR][i][1])




    # TYPE n3 Constraints - ОТНОСИТЕЛЬНЫЕ ПОЗИЦИИ
    print("Adding n3 constraints (relative positions)...")

    # 15. Lada (8) находится юго-восточнее Франции (2)
    n3_1 = bdd.false
    for from_, to in southeast_neighbors:
        n3_1 = n3_1 | (p[COUNTRY][from_][2] & p[COMPANY][to][8])
    task = task & n3_1
    print("   1.Lada юго-восточнее Франции")

    # 16. Розовый цвет (7) находится северо-восточнее KIA (4)
    n3_2 = bdd.false
    for from_, to in northeast_neighbors:
        n3_2 = n3_2 | (p[COMPANY][from_][4] & p[COLOR][to][7])
    task = task & n3_2
    print("   2.Розовый цвет северо-восточнее KIA")

    # 17. Ford (7) находится северо-восточнее Германии (1)
    n3_3 = bdd.false
    for from_, to in northeast_neighbors:
        n3_3 = n3_3 | (p[COUNTRY][from_][1] & p[COMPANY][to][7])
    task = task & n3_3
    print("   3.Ford северо-восточнее Германии")

    # 18. Мощность 410 л.с. (5) находится юго-восточнее Китая (3)
    n3_4 = bdd.false
    for from_, to in southeast_neighbors:
        n3_4 = n3_4 | (p[COUNTRY][from_][3] & p[POWER][to][5])
    task = task & n3_4
    print("   4.Мощность 410 л.с. юго-восточнее Китая")

    # 19. Peugeot (2) находится юго-восточнее Китая (3)
    n3_5 = bdd.false
    for from_, to in southeast_neighbors:
        n3_5 = n3_5 | (p[COUNTRY][from_][3] & p[COMPANY][to][2])
    task = task & n3_5
    print("   5.Peugeot юго-восточнее Китая")

    # TYPE n4 Constraints - СОСЕДСКИЕ ОТНОШЕНИЯ
    print("Adding n4 constraints (neighbor relations)...")

    # 20. Корея (4) соседствует с бежевым цветом (5)
    n4_1 = bdd.false
    for a, b in adjacent_neighbors:
        n4_1 = n4_1 | (p[COUNTRY][a][4] & p[COLOR][b][5]) | (p[COUNTRY][b][4] & p[COLOR][a][5])
    task = task & n4_1
    print("   1.Корея соседствует с бежевым цветом")

    # 21. Jaguar (6) соседствует с мощностью 850 л.с. (7)
    n4_2 = bdd.false
    for a, b in adjacent_neighbors:
        n4_2 = n4_2 | (p[COMPANY][a][6] & p[POWER][b][7]) | (p[COMPANY][b][6] & p[POWER][a][7])
    task = task & n4_2
    print("   2.Jaguar соседствует с мощностью 850 л.с.")

    # 22. Китай (3) соседствует с Японией (0)
    n4_3 = bdd.false
    for a, b in adjacent_neighbors:
        n4_3 = n4_3 | (p[COUNTRY][a][3] & p[COUNTRY][b][0]) | (p[COUNTRY][b][3] & p[COUNTRY][a][0])
    task = task & n4_3
    print("   3.Китай соседствует с Японией")

    # 23. Россия (8) соседствует с США (7)
    n4_4 = bdd.false
    for a, b in adjacent_neighbors:
        n4_4 = n4_4 | (p[COUNTRY][a][8] & p[COUNTRY][b][7]) | (p[COUNTRY][b][8] & p[COUNTRY][a][7])
    task = task & n4_4
    print("   4.Россия соседствует с США")

    # 24. Красный цвет (0) соседствует с Geely (3)
    n4_5 = bdd.false
    for a, b in adjacent_neighbors:
        n4_5 = n4_5 | (p[COLOR][a][0] & p[COMPANY][b][3]) | (p[COLOR][b][0] & p[COMPANY][a][3])
    task = task & n4_5
    print("   5.Красный цвет соседствует с Geely")

    # 25. Мощность 100 л.с. (0) соседствует с мощностью 850 л.с. (7)
    n4_6 = bdd.false
    for a, b in adjacent_neighbors:
        n4_6 = n4_6 | (p[POWER][a][0] & p[POWER][b][7]) | (p[POWER][b][0] & p[POWER][a][7])
    task = task & n4_6
    print("   6.Мощность 100 л.с. соседствует с мощностью 850 л.с.")

    # 26. Мощность 130 л.с. (2) соседствует с фиолетовым цветом (6)
    n4_7 = bdd.false
    for a, b in adjacent_neighbors:
        n4_7 = n4_7 | (p[POWER][a][2] & p[COLOR][b][6]) | (p[POWER][b][2] & p[COLOR][a][6])
    task = task & n4_7
    print("   7.Мощность 130 л.с. соседствует с фиолетовым цветом")

    # Ограничения уникальности
    print("Adding uniqueness constraints...")
    for k in range(4):
        print(f"  Property {k}...")
        for j in range(N):
            for i1 in range(N):
                for i2 in range(i1 + 1, N):
                    task = task & ~(p[k][i1][j] & p[k][i2][j])

    print("All constraints built")
    print("Solving...")

    # Проверяем выполнимость
    if task == bdd.false:
        print("No solutions found! Constraints are inconsistent.")
        return

    # Поиск решений
    print("Finding solutions...")

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

    positions = [
        "0 ЛВ", "1 В", "2 ПВ",
        "3 Л", "4 Ц", "5 П",
        "6 ЛН", "7 Н", "8 ПН"
    ]

    valid_solutions = 0
    max_solutions = 2000

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

        print(f"\n--- Решение {valid_solutions} ---")
        print("Позиция  | Страна   | Компания | Мощность | Цвет")
        print("-" * 80)

        for i in range(N):
            country_name, company_name, power_name, color_name = solution_data[i]
            print(f"{positions[i]}: {country_name:8} | {company_name:8} | "
                  f"{power_name:>6} | {color_name:8}")

        if valid_solutions >= max_solutions:
            break

    print(f"\nTotal solutions found: {valid_solutions}")


if __name__ == "__main__":
    start_time = time.time()
    solve_factories_bdd_dd()
    end_time = time.time()
    print(f"\nВремя выполнения: {end_time - start_time:.2f} секунд")