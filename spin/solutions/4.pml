bit w1 = 0;
bit w2 = 0;
bit w3 = 0;
bit m1 = 0;
bit m2 = 0;
bit m3 = 0;
bit boat = 0;

#define PRINTF_STATUS printf("Кто где: %d %d %d %d %d %d\n", m1, m2, m3, w1, w2, w3)

#define GOAL (w1 && w2 && w3 && m1 && m2 && m3)

active proctype Transfer() {
    do
    :: (boat == w1) -> atomic { printf("Невеста #1 переплыла с берега %d на берег %d\n", w1, !w1); w1 = !w1; boat = !boat; PRINTF_STATUS; }
    :: (boat == w2) -> atomic { printf("Невеста #2 переплыла с берега %d на берег %d\n", w2, !w2); w2 = !w2; boat = !boat; PRINTF_STATUS; }
    :: (boat == w3) -> atomic { printf("Невеста #3 переплыла с берега %d на берег %d\n", w3, !w3); w3 = !w3; boat = !boat }

    :: (boat == m1) -> atomic { printf("Жених #1 переплыл с берега %d на берег %d\n", m1, !m1); m1 = !m1; boat = !boat; PRINTF_STATUS; }
    :: (boat == m2) -> atomic { printf("Жених #2 переплыл с берега %d на берег %d\n", m2, !m2); m2 = !m2; boat = !boat; PRINTF_STATUS; }
    :: (boat == m3) -> atomic { printf("Жених #3 переплыл с берега %d на берег %d\n", m3, !m3); m3 = !m3; boat = !boat; PRINTF_STATUS; }

    :: (boat == m1 && boat == m2) -> atomic { printf("Женихи #1 и #2 переплыли с берега %d на берег %d\n", m1, !m1); m1 = !m1; m2 = !m2; boat = !boat; PRINTF_STATUS; }
    :: (boat == m2 && boat == m3) -> atomic { printf("Женихи #2 и #3 переплыли с берега %d на берег %d\n", m2, !m2); m2 = !m2; m3 = !m3; boat = !boat; PRINTF_STATUS; }
    :: (boat == m1 && boat == m3) -> atomic { printf("Женихи #1 и #3 переплыли с берега %d на берег %d\n", m1, !m1); m1 = !m1; m3 = !m3; boat = !boat; PRINTF_STATUS; }

    :: (boat == w1 && boat == w2) -> atomic { printf("Невесты #1 и #2 переплыли с берега %d на берег %d\n", w1, !w1); w1 = !w1; w2 = !w2; boat = !boat; PRINTF_STATUS; }
    :: (boat == w2 && boat == w3) -> atomic { printf("Невесты #2 и #3 переплыли с берега %d на берег %d\n", w2, !w2); w2 = !w2; w3 = !w3; boat = !boat; PRINTF_STATUS; }
    :: (boat == w1 && boat == w3) -> atomic { printf("Невесты #1 и #3 переплыли с берега %d на берег %d\n", w1, !w1); w1 = !w1; w3 = !w3; boat = !boat; PRINTF_STATUS; }

    :: (boat == m1 && boat == w1) -> atomic { printf("Жених и невеста #1 переплыли с берега %d на берег %d\n", m1, !m1); m1 = !m1; w1 = !w1; boat = !boat; PRINTF_STATUS; }
    :: (boat == m2 && boat == w2) -> atomic { printf("Жених и невеста #2 переплыли с берега %d на берег %d\n", m2, !m2); m2 = !m2; w2 = !w2; boat = !boat; PRINTF_STATUS; }
    :: (boat == m3 && boat == w3) -> atomic { printf("Жених и невеста #3 переплыли с берега %d на берег %d\n", m3, !m3); m3 = !m3; w3 = !w3; boat = !boat; PRINTF_STATUS; }
    od
}

ltl { !(<>GOAL) }
