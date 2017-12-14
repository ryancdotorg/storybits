(function() {
  var eow = String.fromCharCode(0);

  var __Trie = function(initTrie) {
    if (this.constructor !== __Trie) throw new Error("missing 'new'");
    var self = this;
    self._trie = initTrie || {};
    self._prefix = '';

    self._add = function(trie, words) {
      var word, i, _len;
      words = words.constructor === Array ? [].concat.apply([], words) : [words];

      for (_len = words.length, i = 0; i < _len; ++i) {
        word = words[i];
        if (word) {
          trie[word[0]] = (trie[word[0]] || {});
          self._add(trie[word[0]], [word.slice(1)]);
        } else {
          trie[eow] = (trie[eow] || void 0);
        }
      }
    };

    self.add = function() {
      var words = Array.prototype.slice.call(arguments, 0);
      return self._add(self._trie, words);
    };

    self._hasPrefix = function(trie, prefix) {
      if (prefix === '') return true;
      if (!(prefix[0] in trie)) return false;
      return self._hasPrefix(trie[prefix[0]], prefix.slice(1));
    }

    self.hasPrefix = function(prefix) { return self._hasPrefix(self._trie, prefix); };

    self.hasWord = function(word) { return self.hasPrefix(word + eow); };

    self._subTrie = function(trie, prefix) {
      var i, _len;
      if (!self._hasPrefix(trie, prefix)) return void 0;
      for (_len = prefix.length, i = 0; i < _len; ++i) {
        if (!(prefix[i] in trie)) return void 0;
        trie = trie[prefix[i]];
      }
      return trie;
    };

    self.subTrie = function(prefix) {
      var obj, trie;
      trie = self._subTrie(self._trie, prefix);
      obj = new __Trie(trie);
      obj._prefix = self._prefix + prefix;
      return obj;
    }

    self._toArray = function(trie, prefix) {
      var letter, ret = [];
      prefix = (prefix || '');
      for (letter in trie) {
        if (letter === eow) {
          ret.push(prefix);
        } else {
          ret = ret.concat(self._toArray(trie[letter], prefix+letter));
        }
      }
      return ret;
    };

    self.toArray = function() { return self._toArray(self._trie, self._prefix); };

    return self;
  };

  if (typeof module === 'object' && 'exports' in module) {
    module.exports = __Trie;
  } else if (typeof window === 'object') {
    window['Trie'] = __Trie;
  } else {
    return __Trie;
  }
})();
