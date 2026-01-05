mtype {EMPTY, READY, FILLED, READY_ACK, FILLING, FILLING_ACK}

mtype {STATUS_QUERY, REQ_FILLING}
mtype {STATUS_QUERY_ACK, REQ_FILLING_ACK}

mtype vessel_state = EMPTY;
bool in_open = false;
bool out_open = false;

chan blue = [2] of {mtype}
chan red = [2] of {mtype}

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

init {
    blue!STATUS_QUERY;
}

// proctype Vessel() {
//
// }
