extern int __mark(int);
int sumItems(int *items, int itemCount, int *onlineItems, int onlineItemCount, int paidOnline) {

   int sum = 0;
   int i = 0;

   while(__mark(42) & i < itemCount || i < onlineItemCount) {
      if(i < itemCount) sum = sum + items[i];
      if(i < onlineItemCount) sum = sum + onlineItems[i];
      i++;
   }

   sum = sum - paidOnline;

   return sum;
}
