#define N 3

byte boys_left = 2;
byte boys_right = 0;
byte soldiers_left = N;
byte soldiers_right = 0;
byte boat_side = 0; // 0: лодка на левом берегу

#define GOAL (boys_right == 2 && soldiers_right == N && boat_side)	

active proctype main() {
    do
    :: (boat_side == 0) && (boys_left == 2) ->
        atomic { printf("2 boys to right\n"); boys_left = boys_left - 2;
        boys_right = boys_right + 2;
        boat_side = 1 - boat_side;}
		
	:: (boat_side == 1) && (boys_right == 2) ->
        atomic { printf("2 boys to left\n"); boys_right = boys_right - 2;
        boys_left = boys_left + 2;
        boat_side = 1 - boat_side;}
		
	:: (boat_side == 0 && boys_left >= 1) ->
        atomic { printf("1 boy to right\n"); boys_left = boys_left - 1;
        boys_right = boys_right + 1;
        boat_side = 1 - boat_side;}
		
    :: (boat_side == 1 && boys_right >= 1) ->
        atomic { printf("1 boy to left\n"); boys_right = boys_right - 1;
        boys_left = boys_left + 1;
        boat_side = 1 - boat_side;}
		
    :: (boat_side == 0 && soldiers_left >= 1) ->
        atomic { printf("solder to right\n"); soldiers_left = soldiers_left - 1;
        soldiers_right = soldiers_right + 1;
        boat_side = 1 - boat_side;}
		
	:: (boat_side == 1 && soldiers_right >= 1) ->
        atomic { printf("solder to left\n"); soldiers_right = soldiers_right - 1;
        soldiers_left = soldiers_left + 1;
        boat_side = 1 - boat_side;}
    od;
}

ltl {
	!<>GOAL
}