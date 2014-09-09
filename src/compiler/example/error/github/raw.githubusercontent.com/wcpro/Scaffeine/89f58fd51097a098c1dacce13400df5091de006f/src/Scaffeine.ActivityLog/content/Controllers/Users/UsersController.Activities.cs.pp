namespace $rootnamespace$.Controllers.Users
{
    using System.Collections.Generic;
    using Core.Interfaces.Service;
    using Core.Model;
    using System.Web.Mvc;
    using Models.Users;
    using Omu.ValueInjecter;

    public partial class UsersController
    {
        public ActionResult Activities(int id, int page = 1, int pageSize = 10)
        {
            var user = UserService.GetById(id);
            var model = new UserActivitiesViewModel();
            if (user != null)
            {
                var service = DependencyResolver.Current.GetService<IUserActivitiesService>();
                IEnumerable<UserActivities> activities = service.Find(a => a.UserId == id);
                
                model.InjectFrom<UnflatLoopValueInjection>(user);
                model.Activities = activities;
            }
            return View(model);
        }
    }
}
