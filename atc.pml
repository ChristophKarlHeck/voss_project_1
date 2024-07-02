/*
Air Traffic Control (ATC) for a small airport by
Yagdi, Yasin
Maier, Niklas
Heck, Christoph
*/ 

#define F1 ([] <> Airplane[1]@approaching -> [] <> Airplane[1]@on_runway_in)
#define F2 ([] <> Airplane[2]@approaching -> [] <> Airplane[2]@on_runway_in)
#define F3 ([] <> Airplane[3]@approaching -> [] <> Airplane[3]@on_runway_in)
#define F4 ([] <> Airplane[4]@approaching -> [] <> Airplane[4]@on_runway_in)
#define F5 ([] <> Airplane[5]@approaching -> [] <> Airplane[5]@on_runway_in)

#define F (F1 && F2 && F3 && F4 && F5)



mtype = {cleared_to_land, cleared_for_take_off, cleared_to_taxi_in, cleared_to_taxi_out, go_around}
chan radio = [0] of {mtype}

int airplane_on_runway_in = 0;
int airplane_on_runway_out = 0;
int airplane_on_taxiway_in = 0;
int airplane_on_taxiway_out = 0;
int airplane_at_gate = 0;
int airport_capacity = 4;

/*LTL*/
//ltl p1 { [] (airplane_on_runway_in + airplane_on_runway_out <= 1) } // safety property
//ltl p2 { [] (airplane_on_taxiway_in + airplane_on_taxiway_out <= 2) } // safety property
//ltl p3 { [] (airplane_at_gate <= 2)} // safety property
//ltl p4 {  F -> (([] <> Airplane[1]@on_runway_in) && ([] <> Airplane[1]@on_runway_out))  }

//ltl p5 { F -> ([]<> Airplane[1]@on_taxiway_in && []<> Airplane[2]@on_taxiway_in && []<> Airplane[3]@on_taxiway_in && []<> Airplane[4]@on_taxiway_in && []<> Airplane[5]@on_taxiway_in)}

ltl p6 {F -> [](Airplane[1]@approaching -> <>Airplane[1]@at_gate)}

active [1] proctype Tower() {
	do
	/* Cleared to land */
	:: (!airplane_on_runway_in && !airplane_on_runway_out && airport_capacity > 0) ->
	atomic {
		radio!cleared_to_land;
		airport_capacity--;
		airplane_on_runway_in ++;
	}
	/* Cleared to taxi in*/
	/*airport_capacity < 4 to make sure that at least one airplane is on the airport*/
	:: (!airplane_on_taxiway_in && airplane_on_runway_in) ->
	atomic {
		airplane_on_taxiway_in ++;
		radio!cleared_to_taxi_in;
	}
	/* Cleared to taxi out*/
	:: (airplane_at_gate > 0  && !airplane_on_taxiway_out)->
	atomic { 
		airplane_on_taxiway_out ++;
		radio!cleared_to_taxi_out;
	}
	/* Cleared for take off */
	:: (!airplane_on_runway_out && !airplane_on_runway_in && airplane_on_taxiway_out) -> 
		atomic{
			airplane_on_runway_out ++;
			radio!cleared_for_take_off
		}

	/* Go around */
	:: (airport_capacity==0) -> radio!go_around;
	od;

}

active [5] proctype Airplane() {

	in_air:
		do
		:: goto approaching;
		od;

	approaching:
		if
		::	atomic {
			radio?cleared_to_land ->
				goto on_runway_in;
			}
		:: radio?go_around -> goto in_air;
		fi;

	on_runway_in:
		atomic {
			radio?cleared_to_taxi_in;
			airplane_on_runway_in --;
			goto on_taxiway_in;
		}

	on_taxiway_in:
		atomic { airplane_at_gate < 2 ->
			airplane_on_taxiway_in --;
			airplane_at_gate ++;
			goto at_gate;
		}

	at_gate:
		atomic { radio?cleared_to_taxi_out ->
				airplane_at_gate --;
				goto on_taxiway_out;
		}

	on_taxiway_out:
		atomic {
			radio?cleared_for_take_off;
			airplane_on_taxiway_out --;
			goto on_runway_out;
		}

	on_runway_out:
		atomic {  
			airplane_on_runway_out --;
			airport_capacity++;
			goto in_air;
		}


		

}

// active proctype monitor()
// {
// 	assert(!deadlock)
// }