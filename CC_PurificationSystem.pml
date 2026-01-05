mtype = {
    EMPTY, READY, FILLED,
    STATUS_QUERY, STATUS_QUERY_ACK,
    REQ_FILLING, REQ_FILLING_ACK,
    READY_ACK, FILLING, FILLING_ACK,
    OPEN, CLOSE
};
mtype vessel_state = EMPTY;

chan blue = [2] of {mtype};
chan red = [2] of {mtype};
chan vessel = [2] of {mtype};
chan inCtrl_commmd = [2] of {mtype};
chan outCtrl_command = [2] of {mtype};

proctype InCtrl() { 
    mtype current_state; 
    do 
        :: blue!STATUS_QUERY; 
            blue?STATUS_QUERY_ACK; 
            red?current_state; 
        // current_state: EMPTY/READY/FILLED 
        // next: if vessel_state==EMPTY then blue!REQ_FILLING ...
    od 
}

active proctype OutCtrl() {
    do
        :: blue?eval(STATUS_QUERY) -> {
            // send status query ack
            blue!STATUS_QUERY_ACK;
            printf("[out controller] (blue) sent status query\n");

            // send status
            red!vessel_state;
            printf("[out controller] (red) sent status\n");
        }
    od
}

// proctype InValve() {
//
// }

// proctype OutValve() {
//
// }   

init {
    blue!STATUS_QUERY;
}
