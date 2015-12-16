/*@ rel_in (and (forall ((i Int)) (= (select HEAP$1 i) (select HEAP$2 i))) (let ((server-state (select HEAP$2 (+ server$2 (* 682 0) 160)))) (or (= 2 server-state) (= 3 server-state) (> server-state 11) (< server-state 2)))) @*/
#include "server.h"

int slaveIsInHandshakeState(void) {
    return (server.repl_state >= REPL_STATE_RECEIVE_PONG &&
            server.repl_state <= REPL_STATE_RECEIVE_PSYNC) ? 1 : 0;
}


void undoConnectWithMaster(void) {
    int fd = server.repl_transfer_s;

    serverAssert(server.repl_state == REPL_STATE_CONNECTING ||
                 slaveIsInHandshakeState());
    aeDeleteFileEvent(server.el,fd,AE_READABLE|AE_WRITABLE);
    close(fd);
    server.repl_transfer_s = -1;
    server.repl_state = REPL_STATE_CONNECT;
}
