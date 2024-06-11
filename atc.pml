/*
Air Traffic Control (ATC) for a small airport by
Yagdi, Yasin
Maier, Niklas
Heck, Christoph
*/ 



mtype = {cleared_to_land, cleared_for_take_off, cleared_to_taxi_in, cleared_to_taxi_out, go_around}
chan radio = [0] of {mtype}

int airplane_on_runway = 0;
int airplane_on_taxiway = 0;
bool airplane_are_waiting_take_off = false;
int airport_capacity = 4

/*LTL*/
//ltl p1 { [] (airplane_on_runway <= 1) } // safety property
//ltl p2 { [] (airplane_on_taxiway <= 2) } // safety property

active [1] proctype Tower() {
	do
	/* Cleared to land */
	:: (!airplane_on_runway && !airplane_on_taxiway && airport_capacity > 0) ->
	atomic {
		radio!cleared_to_land;
		airport_capacity--;
		airplane_on_runway = airplane_on_runway + 1;
	}
	/* Cleared to taxi in*/
	/*airport_capacity < 4 to make sure that at least one airplane is on the airport*/
	:: (!airplane_on_taxiway && airplane_on_runway && !airplane_are_waiting_take_off) ->
	atomic {
		airplane_on_taxiway = airplane_on_taxiway + 1;
		radio!cleared_to_taxi_in;
	}
	/* Cleared to taxi out*/
	:: atomic { 
		(!airplane_on_taxiway && !airplane_on_runway && airport_capacity < 4) ->
	
		airplane_on_taxiway = airplane_on_taxiway + 1;
		radio!cleared_to_taxi_out;
	}
	/* Cleared for take off */
	:: (!airplane_on_runway && airplane_on_taxiway && airplane_are_waiting_take_off) -> 
		atomic{
			airplane_on_runway = airplane_on_runway + 1;
			radio!cleared_for_take_off
		}

	/* Go around */
	:: (airport_capacity==0) -> radio!go_around;
	od;

}

active [5] proctype Airplane() {

	bool direction = true /* true: in; false: out */

	in_air:
		do
		:: goto approaching;
		od;

	approaching:
		if
		::	atomic {
			radio?cleared_to_land ->
				direction = true;
				goto on_runway;
			}
		:: radio?go_around -> goto in_air;
		fi;

	on_runway:
		if
		:: direction -> 
		atomic {
			radio?cleared_to_taxi_in;
			airplane_on_runway = airplane_on_runway - 1;
			goto on_taxiway;
		}
		:: atomic { else -> 
			airplane_on_runway = airplane_on_runway - 1;
			airplane_are_waiting_take_off = false;
			goto in_air;
		}
		fi;

	on_taxiway:
		if
		:: atomic {
			direction ->
				airplane_on_taxiway = airplane_on_taxiway - 1;
			 	goto at_gate;
		}
		:: else -> 
		atomic {
			radio?cleared_for_take_off;
			airplane_on_taxiway = airplane_on_taxiway - 1;
			airport_capacity++; /**critical section */
			goto on_runway;
		}
		fi;

	at_gate:
		if
		::  radio?cleared_to_taxi_out;
		atomic {
			!airplane_on_runway -> 
			airplane_are_waiting_take_off = true;
			direction = false;
			goto on_taxiway;
		}
	 	fi;

		

}

// active proctype monitor()
// {
// 	assert(!deadlock)
// }