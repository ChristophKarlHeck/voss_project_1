/*
Air Traffic Control (ATC) for a small airport by
Yagdi, Yasin
Maier, Niklas
Heck, Christoph
*/ 

mtype = {digits, on_hook}
chan line = [0] of {mtype}



active [1] proctype Tower() {

}

active [1] proctype Airport() {

}

active [1] proctype Airplane() {

}

active proctype monitor()
{
	assert(!deadlock)
}