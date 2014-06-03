namespace $rootnamespace$.Controllers.Account
{
    using System;
    using System.Collections.Generic;
    using System.Linq;
    using System.Web.Mvc;

    using AutoMapper;
    using Core.Model;
    using Extensions;
    using Models;
    using Omu.ValueInjecter;

    public partial class AccountController
    {
        [HttpGet]
        public new ActionResult Profile()
        {
            var model = new ProfileModel();

            model.InjectFrom<UnflatLoopValueInjection>(this.GetCurrentUser());

            return View(model);
        }

        [HttpPost]
        public new ActionResult Profile(ProfileModel model)
        {
            if (ModelState.IsValid)
            {
                if (string.Compare(this.GetCurrentUser().Email, model.Email, StringComparison.InvariantCultureIgnoreCase) != 0)
                {
                    var inUse = _userService.Find(u => u.Email == model.Email).Any();
                    if (inUse)
                    {
                        ModelState.AddModelError("EmailInUse", "Email already in use");
                    }
                }

                this.GetCurrentUser().InjectFrom<UnflatLoopValueInjection>(model);

                try
                {
					_userService.SaveOrUpdate(this.GetCurrentUser());
                    TempData["Success"] = "User was successfully updated.";
                    return RedirectToAction("Profile");
                }
                catch (Exception)
                {
                    ModelState.AddModelError("Exception", "Unexpected error");
                }                
            }

            return View(model);
        }

        [HttpGet]
        public ActionResult Emails()
        {
            Mapper.CreateMap<UserEmail, EmailModel>();

            var user = this.GetCurrentUser();

            List<UserEmail> model = _userEmailService.Find(x => x.UserId == user.Id).ToList();

            ViewBag.DefaultEmail = this.GetCurrentUser().Email;

            return View(model);
        }

        [HttpPost]
        public ActionResult Emails(UserEmail model)
        {
            model.UserId = this.GetCurrentUser().Id;
            if (ModelState.IsValid)
            {
                _userEmailService.SaveOrUpdate(model);
                TempData["Success"] = "Email was successfully added";
            }

            return RedirectToAction("Emails");
        }       
    }
}
