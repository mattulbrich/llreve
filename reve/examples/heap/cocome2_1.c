/*@ rel_in
      (and (= items$1 items$2)
           (= itemCount$1 itemCount$2)
           (= onlineItems$1 onlineItems$2)
           (= onlineItemCount$1 onlineItemCount$2)
           (= paidOnline$1 paidOnline$2)
           (= onlineItemCount$1 0)
           (= paidOnline$1 0)
           (= HEAP$1 HEAP$2)) @*/
extern int __mark(int);

int sumItems(int *items, int itemCount, int *onlineItems, int onlineItemCount, int paidOnline) {

   int sum = 0;
   int i = 0;
   int j = 0;

   while(__mark(42) & (i < itemCount || j < onlineItemCount)) {
      if(i < itemCount) sum = sum + items[i];
      if(j < onlineItemCount) sum = sum + onlineItems[j];
      i++;
      j++;
   }

   sum = sum - paidOnline;

   return sum;
}
