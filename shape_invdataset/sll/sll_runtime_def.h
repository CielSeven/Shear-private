struct list* malloc_list(int data)
/*@ With data0 
    Require data == data0 && emp
    Ensure __return != 0 && __return -> data == data0 && __return -> next == 0
*/;

void free_list(struct list * x)
/*@ With d n 
    Require x -> data == d && x -> next == n
    Ensure emp
*/;