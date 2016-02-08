/* openbsd */
extern int __mark(int);
char *
stpcpy(char *to, const char *from)
{
	for (; __mark(0) & ((*to = *from) != '\0'); ++from, ++to);
	return(to);
}
