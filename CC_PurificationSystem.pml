mtype {EMPTY, READY, FILLED, READY_ACK, FILLING, FILLING_ACK,
       STATUS_QUERY, REQ_FILLING, 
       STATUS_QUERY_ACK, REQ_FILLING_ACK,
       OPEN, CLOSE}

chan blue = [2] of {mtype}
chan red = [2] of {mtype}
chan vessel = [6] of {mtype}
chan inCtrl_commmd = [2] of {mtype}
chan outCtrl_command = [2] of {mtype}

// proctype InCtrl() {
//
// }

active proctype OutCtrl() {
    mtype message;
    do
        :: blue?message; message == STATUS_QUERY -> {
            // send status query ack
            red!STATUS_QUERY_ACK;
            printf("[out controller] (red) sent status query\n");

            // send status
            blue!vessel_state;
            printf("[out controller] (blue) sent status\n");
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
