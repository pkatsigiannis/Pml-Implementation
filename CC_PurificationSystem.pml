mtype = {
    EMPTY, READY, FILLED,
    STATUS_QUERY, STATUS_QUERY_ACK,
    REQ_FILLING, REQ_FILLING_ACK,
    READY_ACK, FILLING, FILLING_ACK,
    OPEN, CLOSE
};

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
