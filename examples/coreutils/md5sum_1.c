typedef int bool;
typedef int size_t;

extern int __mark(int);
#define false (0)
#define true  (1)
#define ISWHITE(c) ((c) == ' ' || (c) == '\t')

bool
bsd_split_3 (char *s, size_t s_len, unsigned char **hex_digest, char **file_name)
{
  size_t i;

  *file_name = s;

  /* Find end of filename. The BSD 'md5' and 'sha1' commands do not escape
     filenames, so search backwards for the last ')'. */
  i = s_len - 1;
  while (__mark(1) & (i && s[i] != ')'))
    i--;

  if (s[i] != ')')
    return false;

  s[i++] = '\0';

  while (__mark(2) & (ISWHITE (s[i])))
    i++;

  if (s[i] != '=')
    return false;

  i++;

  while (__mark(3) & (ISWHITE (s[i])))
    i++;

  *hex_digest = (unsigned char *) &s[i];
  return true;
}
