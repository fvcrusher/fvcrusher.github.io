bit father = 0;
bit mother = 0;
bit son = 0;
bit dauther = 0;
bit torch = 0;
byte elapsed_time = 0;

#define FATHER_TIME 1
#define MOTHER_TIME 2
#define SON_TIME 4
#define DAUGTHER_TIME 5
#define TORCH_TIME 12

#define STATUS printf("Кто где: %d %d %d %d, Прошло %d минут\n", father, mother, son, dauther, elapsed_time)

#define GOAL (father && mother && son && dauther && elapsed_time <= TORCH_TIME)

active proctype Tunnel() {
    do    
    :: (father == torch && elapsed_time < TORCH_TIME) ->  atomic { printf("Отец прошел из %d в %d", father, !father);    elapsed_time = elapsed_time + FATHER_TIME;    father = !father;    torch = !torch;  STATUS; }
    :: (mother == torch && elapsed_time < TORCH_TIME) ->  atomic { printf("Мать прошла из %d в %d", mother, !mother);    elapsed_time = elapsed_time + MOTHER_TIME;    mother = !mother;    torch = !torch;  STATUS; }
    :: (son == torch && elapsed_time < TORCH_TIME) ->     atomic { printf("Сын прошел из %d в %d", son, !son);           elapsed_time = elapsed_time + SON_TIME;       son = !son;          torch = !torch;  STATUS; }
    :: (dauther == torch && elapsed_time < TORCH_TIME) -> atomic { printf("Дочь прошла из %d в %d", dauther, !dauther);  elapsed_time = elapsed_time + DAUGTHER_TIME;  dauther = !dauther;  torch = !torch;  STATUS; }

    :: (father == torch && mother == torch && elapsed_time < TORCH_TIME) ->  atomic { printf("Отец и мать прошли из %d в %d", father, !father);  elapsed_time = elapsed_time + MOTHER_TIME;    father = !father;  mother =! mother;    torch = !torch;  STATUS; }
    :: (father == torch && son == torch && elapsed_time < TORCH_TIME) ->     atomic { printf("Отец и сын прошли из %d в %d", father, !father);   elapsed_time = elapsed_time + SON_TIME;       father = !father;  son =! son;          torch = !torch;  STATUS; }
    :: (father == torch && dauther == torch && elapsed_time < TORCH_TIME) -> atomic { printf("Отец и дочь прошли из %d в %d", father, !father);  elapsed_time = elapsed_time + DAUGTHER_TIME;  father = !father;  dauther =! dauther;  torch = !torch;  STATUS; }
    :: (mother == torch && son == torch && elapsed_time < TORCH_TIME) ->     atomic { printf("Мать и сын прошли из %d в %d", mother, !mother);   elapsed_time = elapsed_time + SON_TIME;       mother = !mother;  son =! son;          torch = !torch;  STATUS; }
    :: (mother == torch && dauther == torch && elapsed_time < TORCH_TIME) -> atomic { printf("Мать и дочь прошли из %d в %d", mother, !mother);  elapsed_time = elapsed_time + DAUGTHER_TIME;  mother = !mother;  dauther =! dauther;  torch = !torch;  STATUS; }
    :: (son == torch && dauther == torch && elapsed_time < TORCH_TIME) ->    atomic { printf("Сын и дочь прошли из %d в %d", son, !son);         elapsed_time = elapsed_time + DAUGTHER_TIME;  son = !son;        dauther =! dauther;  torch = !torch;  STATUS; }
    od
}

ltl { !(<>GOAL); }
