/*@ rel_in
    (and
      (forall
         ((i Int))
         (= (select HEAP$1 i) (select HEAP$2 i)))
      (let
          ((server-state (select HEAP$2 (+ server$2 (* 682 0) 160))))
        (or (= 2 server-state) (= 3 server-state) (> server-state 11) (< server-state 2))))
@*/
#define REPL_STATE_CONNECTING 2 /* Connecting to master */
#define AE_READABLE 1
#define AE_WRITABLE 2
#define REPL_STATE_RECEIVE_PONG 3 /* Wait for PING reply */
#define REPL_STATE_RECEIVE_PSYNC 11 /* Wait for PSYNC reply */
#define REPL_STATE_CONNECT 1 /* Must connect to master */
#define serverAssert(_e) ((_e)?(void)0 : (_serverAssert(#_e,__FILE__,__LINE__),_exit(1)))
extern void _serverAssert(char *estr, char *file, int line);
extern void aeDeleteFileEvent(int *eventLoop, int fd, int mask);
extern int close(int fd);
extern void _exit(int);
extern struct redisServer server;
struct redisServer {
    int *el;
    int repl_state;          /* Replication status if the instance is a slave */
    int repl_transfer_s;     /* Slave -> Master SYNC socket */
};

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
