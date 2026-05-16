<?php

use Illuminate\Database\Migrations\Migration;
use Illuminate\Database\Schema\Blueprint;
use Illuminate\Support\Facades\Schema;

return new class extends Migration
{
    /**
     * Run the migrations.
     */
    public function up(): void
    {
        if(!Schema::hasTable('broker')) {

            Schema::create('broker', function (Blueprint $table) {
                $table->id('broker_id');
                $table->string('broker_name');
                $table->string('category');
                $table->string('cin_no');
                $table->string('address');
                $table->string('contact_no');
                $table->string('email');
                $table->string('irdia_registration_no');
                $table->string('favicon_icon')->nullable();
                $table->string('logo')->nullable();
                $table->string('sign_in_option')->nullable();
                $table->string('status')->default('Y');
                $table->timestamps();
            });
        }
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        Schema::dropIfExists('broker');
    }
};
