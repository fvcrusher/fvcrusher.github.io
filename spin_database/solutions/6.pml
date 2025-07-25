// Решите с помощью SPIN следующую головоломку («Отец и сыновья»). Отец вместе с
// двумя сыновьями и лодкой находится на берегу реки. Переправиться через реку
// можно только в лодке, грузоподъемность которой составляет 200 фунтов. Все
// трое умеют управлять лодкой. Отец весит 200 фунтов, а оба сына — по 100
// фунтов. Как им переправиться вместе с лодкой через реку?

// Вариант решения:
// 1. Оба сына переправляются на второй берег
// 2. Один сын остается на береге, а второй возвращается.
// 3. Отец переплывает на второй берег
// 4. Сын возвращается на первый берег
// 5. Оба сына переправляются на второй берег

bit boat = 0;
bit father = 0;
bit son_1 = 0;
bit son_2 = 0;

#define GOAL (boat && father && son_1 && son_2)

active proctype main() {
	do
	:: (boat == father) -> atomic {
		printf("Отец переплывает\n");
		boat = 1 - boat;
		father = boat;
	}

	:: (boat == son_1) -> atomic {
		printf("Сын 1 переплывает\n");
		boat = 1 - boat;
		son_1 = boat;
	}

	:: (boat == son_2) -> atomic {
		printf("Сын 2 переплывает\n");
		boat = 1 - boat;
		son_2 = boat;
	}

	:: (boat == son_1 && boat == son_2) -> atomic {
		printf("Оба сына переплывают\n");
		boat = 1 - boat;
		son_1 = boat;
		son_2 = boat;
	}

	od
}

ltl { !(<>GOAL) }
