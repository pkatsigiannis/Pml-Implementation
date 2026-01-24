chan c = [4] of {int, int}

proctype S1() {
       	atomic { c!1,2; c!1,1; c!2,1; c!0,1; }
}

proctype S2() {
       	atomic { c!!1,2; c!!1,1;c!!2,1; c!!0,1 }
}
	
proctype R1() {
	int v1, v2
  	do
  	:: c?v1,v2 ->
  	   printf("(%d,%d)\n", v1, v2)
  	od
}

proctype R2() {
	int v1 = 9
	do
    	:: !(c?[v1,1]) -> printf("Cannot receive first element from buffered channel! Switching to random receive...\n") -> 
    		do 
    		:: c?? <v1,1> -> printf("(%d,%d)\n", v1, 1)
    		:: !(c??[v1,1]) -> break
    		//:: else -> break
    		od; 
    		break
    	:: else -> c?v1,1 -> printf("(%d,%d)\n", v1, 1)
    	od
 /*
 A subtle point here: SPIN disallows "else -> break" branches in loops that contain receive operations as guards of other branches.
 This happens because receive operations are disabled (false) if the corresponding channel is empty. But an empty channel is an 
 ephemeral state that should not form a reason for breaking a loop.
 */
    	
}

init {
	run S1();
	run R2()
}