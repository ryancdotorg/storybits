(function() {
  // scoping
  var wm_Trie, wm_getEditDistance;

  var _log = function(msg) {
    if (typeof log == 'function') {
      log(msg);
    } else {
      console.log(msg);
    }
  };

  var __WordMapper = function(wordlists, asyncInit) {
    if (this.constructor !== __WordMapper) throw new Error("missing 'new'");

    // set up wm_Trie and wm_getEditDistance if we haven't already
    wm_Trie = wm_Trie || typeof Trie !== 'undefined' ? Trie : require('./trie');
    wm_getEditDistance = wm_getEditDistance || typeof getEditDistance !== 'undefined' ? getEditDistance : require('./editdist');

    var self = this;
    self.wordlists = wordlists;
    self.lengths = [];

    self._w2li = {};
    self._li2w = {};
    self._trie = new wm_Trie();
    self._etrie = new wm_Trie();

    self._etrie_built = false;

    self.edits = function(word) {
      var ret = [], uniq = {}, i, j, t, _len, edit, z = {};
      var letters = 'abcdefghijklmnopqrstuvwxyz';

      // need an array so we can make changes
      word = word.split('');

      // transposition
      for (_len = word.length - 1, i = 0; i < _len; ++i) {
        edit = word.slice(0);
        // make sure the edit would change something
        if (edit[i] !== edit[i+1]) {
          t = edit[i]; edit[i] = edit[i+1]; edit[i+1] = t; 
          uniq[edit.join('')] = z;
        }
      };

      // replacement + deletion
      for (_len = word.length, i = 0; i < _len; ++i) {
        edit = word.slice(0);
        // replace
        for (j = 0; j < 26; ++j) {
          // make sure the edit would change something
          if (word[i] !== letters[j]) {
            edit[i] = letters[j];
            uniq[edit.join('')] = z;
          }
        }
        // delete
        edit.splice(i, 1);
        uniq[edit.join('')] = z;
      }

      // insertion
      for (_len = word.length + 1, i = 0; i < _len; ++i) {
        edit = word.slice(0);
        edit.splice(i, 0, '_');
        for (j = 0; j < 26; ++j) {
          edit[i] = letters[j];
          uniq[edit.join('')] = z;
        }
      };

      for (edit in uniq) if (uniq[edit] === z) ret.push(edit);
      return ret;
    };

    // build word <=> [list, item] tables and trie
    (function() {
      var i, j, k, _len1, _len2, _len3, wordlist, equiv_words, li;
      
      for (_len1 = wordlists.length, i = 0; i < _len1; ++i) {
        wordlist = wordlists[i];
        self.lengths.push(wordlist.length);

        self._li2w[i] = (self._li2w[i] || {});

        for (_len2 = wordlist.length, j = 0; j < _len2; ++j) {
          equiv_words = wordlist[j];
          self._trie.add(equiv_words);

          self._li2w[i][j] = equiv_words[0];

          li = [i, j];

          for (_len3 = equiv_words.length, k = 0; k < _len3; ++k) {
            word = equiv_words[k];
            if (word in self._w2li) throw new Error("non-unique word '" + word + "'");
            self._w2li[word] = li;
          }
        }
      }

      // background initialization
      if (asyncInit) {
        var words = Object.keys(self._w2li);
        _len1 = words.length, i = 0;
        var asyncEdits = function() {
          self._trie.add(self.edits(words[i]));
          if (++i < _len1) {
            if (typeof setImmediate === 'function') {
              setImmediate(asyncEdits);
            } else {
              setTimeout(asyncEdits, 0);
            }
          } else {
            self._etrie_built = true;
            if (typeof asyncInit === 'function') asyncInit();
          }
        };
        asyncEdits();
      } else {
        for (i in self._w2li) self._trie.add(self.edits(i));
        self._etrie_built = true;
      }
    })();

    self.wordsByPrefix = function(prefix) {
      var trie = self._trie.subTrie(prefix);
      if (trie) return trie.toArray();
      return [];
    }

    // go from [list, item] to word
    self.li2w = function(ary) {
      var l = ary[0], i = ary[1];
      if (l in self._li2w && i in self._li2w[l]) return self._li2w[l][i];
      return void 0;
    };

    self.split = function(str) {
      var prefix, suffix, i, _len, word, words, ret, next;
      prefix = str.slice(0, 3);
      words = self.wordsByPrefix(prefix);
      //words.reverse();
      for (_len = words.length, i = 0; i < _len; ++i) {
        word = words[i];
        ret = [str.slice(0, word.length)];
        if (word === ret[0]) {
          suffix = str.slice(word.length);
          if (suffix.length === 0) return ret;
          next = self.split(suffix);
          if (next && next.length > 0) {
            return ret.concat(next);
          }
        }
      }
      return [];
    }

    // XXX currently, this doesn't work as well as the other one
    self._split = function(str) {
      var prefix, suffix, i, li, word, ret, next;
      // XXX should un-hardcode the word lengths
      prefix = str.slice(0, 3);
      if (self._trie.hasPrefix(prefix)) {
        for (i = 3; i < 12; ++i) {
          word = str.slice(0, i);
          li = self.w2li(word);
          if (li) {
            ret = [self.li2w(li)];
            suffix = str.slice(i);
            if (suffix.length === 0) return ret;
            next = self.split(suffix);
            if (next && next.length > 0) return ret.concat(next);
          }
        }
      }
      return [];
    };

    // go from string to [list, item] pairs
    self.s2li = function(str, callback, wait) {
      if (typeof wait == 'undefined') wait = true;
      var ret = [], words, word, _len1, _len1, i, j, li, split;
      if (typeof callback === 'function') {
        var cbwrap = function() {
          if (!wait || self._etrie_built) {
            callback(self.s2li(str));
          } else {
            setTimeout(cbwrap, 10);
          }
        }
        setTimeout(cbwrap, 0);
      }
      str = str.toLowerCase();
      str = str.replace(/[^a-z ]+/g, '');
      str = str.replace(/ +/g, ' ');
      words = str.split(/ +/);
      for (_len1 = words.length, i = 0; i < _len1; ++i) {
        word = words[i];
        li = self.w2li(word);
        // recognized word?
        if (li) {
          ret.push(self.li2w(li));
        } else {
          // maybe it's one or more words mashed together
          split = self.split(word);
          if (split) {
            // yes, was multiple words mashed together. make them canonical.
            for (_len2 = split.length, j = 0; j < _len2; ++j) {
              li = self.w2li(split[j]);
              if (!li) {
                _log('failed to decode: ' + split[j] + ' ' + split[j].length);
                continue;
              }
              ret.push(self.li2w(li));
            }
          }
        }
      }

      return ret;
    };

    // go from word to [list, item] with error correction magic
    self.w2li = function(w) {
      if (w in self._w2li) return self._w2li[w];
      var best_dist = 999, best_word = "", best_count = 0, candidate, dist;
      for (candidate in self._w2li) {
        dist = wm_getEditDistance(w, candidate);
        if (dist == best_dist) {
          if (self._w2li[best_word] !== self._w2li[candidate]) ++best_count;
        } else if (dist < best_dist) {
          best_word = candidate;
          best_dist = dist;
          best_count = 0;
        }
      }
      if (best_dist > 2 || best_count > 0) {
        return void 0;
      } else {
        // cache corrected result
        self._w2li[w] = self._w2li[best_word];
        return self._w2li[w];
      }
    };
  };
  if (typeof module === 'object' && 'exports' in module) {
    module.exports = __WordMapper;
  } else if (typeof window === 'object') {
    window['WordMapper'] = __WordMapper;
  } else {
    return __WordMapper;
  }
})();
/*
vim: sw=2 ts=2 et ai si bg=dark
*/
