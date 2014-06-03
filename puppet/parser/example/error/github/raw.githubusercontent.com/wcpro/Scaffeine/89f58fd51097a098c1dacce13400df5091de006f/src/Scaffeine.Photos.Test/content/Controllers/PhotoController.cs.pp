namespace $rootnamespace$.Controllers
{
    using System.Linq;
    using System.Web;
    using System.Web.Mvc;

    using $rootnamespace$.Photos;
    using $rootnamespace$.Photos.Models;

    public partial class PhotoController : Controller
    {
        public ActionResult Index()
        {
            var photos = PhotoManager.Provider.GetAllPhotoResizes("21_08_2012_10_25_01_5278").Select(c => c.Value).ToList();
            var photo = PhotoManager.Provider.GetPhotoResize("21_08_2012_10_25_01_5278", "Medium");
            var photo2 = PhotoManager.Provider.GetPhotoResize("21_08_2012_10_25_01_5278", "Small");

            var list = new[]
            {
                "21_08_2012_10_25_01_5278", "21_08_2012_10_16_36_1219", "21_08_2012_12_48_47_9774",
                "21_08_2012_10_25_57_8080", "21_08_2012_10_26_06_8916", "21_08_2012_10_28_04_3083"
            };

            var photo3 = PhotoManager.Provider.GetPhotosByResize("Medium", list).ToList();

            return View(photo3);
        }

        public ActionResult PhotoUpload()
        {
            return View();
        }

        [HttpPost]
        public ActionResult PhotoUpload(HttpPostedFileBase file)
        {
            var request = new PhotoRequest(file.InputStream, "image/gif", null);

            var photo = PhotoManager.Provider.SavePhotoForAllSizes(request, true);

            var test = photo.FirstOrDefault();

            return View(test);
        }
    }
}