mtype = {
    EMPTY, READY, FILLED, // vessel state from OutValveCtrl to InValveCtrl over red channel
    ATTENTION, // alert from InValveCtrl to OutValveCtrl over red channel at the end of draining
    STATUS_QUERY, REQ_FILLING, FILLING, // from InValveCtrl to OutValveCtrl over blue channel
    STATUS_QUERY_ACK, REQ_FILLING_ACK, FILLING_ACK, // acks from OutValveCtrl to InValveCtrl over blue channel
    OPEN, CLOSE // commands from controllers to valves over out_cmd and in_cmd channels
};

