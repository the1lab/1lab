module Shake.Markdown where

import Control.Monad.IO.Class (MonadIO)
import Text.Pandoc.Definition (Pandoc)

readLabMarkdown :: MonadIO m => FilePath -> m Pandoc
