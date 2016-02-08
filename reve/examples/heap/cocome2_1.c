/*@ rel_in (and (= items$1_0 items$2_0) (= itemCount$1_0 itemCount$2_0) (= onlineItems$1_0 onlineItems$2_0) (= onlineItemCount$1_0 onlineItemCount$2_0) (= paidOnline$1_0 paidOnline$2_0) (= onlineItemCount$1_0 0) (= paidOnline$1_0 0) (forall ((i Int)) (= (select HEAP$1 i) (select HEAP$2 i)))) @*/
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
