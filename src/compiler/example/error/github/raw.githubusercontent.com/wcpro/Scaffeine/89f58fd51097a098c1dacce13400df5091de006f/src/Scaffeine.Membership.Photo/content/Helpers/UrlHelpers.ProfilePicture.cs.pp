namespace $rootnamespace$.Helpers
{
    using System;
    using System.Web.Mvc;
    using Core.Common.Photos;
    using Core.Model;

    public static partial class UrlHelpers
    {
        public static string ProfilePicture(this UrlHelper url, string photoId, string resize, Gender gender)
        {            
            if (!PhotoManager.PhotoResizes.ContainsKey(resize))
                throw new ArgumentException("'{0}' photo resize is not defined");

            string returnValue = string.Format("~/Content/images/{0}/{1}.jpg", resize, gender.ToString());

            if (!string.IsNullOrWhiteSpace(photoId))
            {
                try
                {
                    var photo = PhotoManager.Provider.GetPhotoResize(photoId, resize);
                    returnValue = photo.Url;
                }
                catch (Exception)
                {
                }
            }

            return url.Content(returnValue);
        }
      
    }
}