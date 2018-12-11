(define-key special-event-map [config-changed-event] 'ignore) ;; ignore GTK default font https://emacs.stackexchange.com/questions/32641/something-changes-the-default-face-in-my-emacs
; (defalias 'dynamic-setting-handle-config-changed-event 'ignore) ;; https://debbugs.gnu.org/cgi/bugreport.cgi?bug=25228
(set-face-attribute 'default nil :height 200)
